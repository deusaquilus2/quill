package io.getquill.sql.norm

import io.getquill.ast.{ Ast, Ident, Property, StatefulTransformer, Transform }
import io.getquill.ast.Visibility.Visible
import io.getquill.context.sql.{ FlatJoinContext, FlattenSqlQuery, FromContext, InfixContext, JoinContext, QueryContext, SelectValue, SetOperationSqlQuery, SqlQuery, TableContext, UnaryOperationSqlQuery }
import io.getquill.norm.{ BetaReduction, PropertyMatroshka, TypeBehavior }
import io.getquill.quat.Quat
import io.getquill.util.Interpolator
import io.getquill.util.Messages.TraceType.NestedQueryExpansion

import scala.collection.mutable
import scala.collection.mutable.LinkedHashSet

/**
 * Filter out unused subquery properties and unhide the ones that are used
 */
object RefineSubqueryProperties {

  val interp = new Interpolator(NestedQueryExpansion, 3)
  //import interp._

  def apply(q: SqlQuery): SqlQuery =
    apply(q, LinkedHashSet.empty, true)

  private def apply(q: SqlQuery, references: LinkedHashSet[Property], isTopLevel: Boolean = false): SqlQuery =
    q match {
      case q: FlattenSqlQuery =>
        expandNested(q, isTopLevel)
      case SetOperationSqlQuery(a, op, b) =>
        SetOperationSqlQuery(apply(a, references), op, apply(b, references))(q.quat)
      case UnaryOperationSqlQuery(op, q) =>
        UnaryOperationSqlQuery(op, apply(q, references))(q.quat)
    }

  private def filterUnused(select: List[SelectValue], references: LinkedHashSet[Property]): List[SelectValue] = {
    val usedAliases = references.map {
      case PropertyMatroshka(_, list) => list.mkString
    }.toSet
    select.filter(sv => sv.alias.forall(aliasValue => usedAliases.contains(aliasValue)))
  }

  private def expandNested(q: FlattenSqlQuery, isTopLevel: Boolean): SqlQuery =
    q match {
      case FlattenSqlQuery(from, where, groupBy, orderBy, limit, offset, select, distinct) =>
        val asts = Nil ++ select.map(_.ast) ++ where ++ groupBy ++ orderBy.map(_.ast) ++ limit ++ offset
        val expansions = q.from.map(expandContext(_, asts))
        val from = expansions.map(_._1)
        val references = expansions.flatMap(_._2)

        val replacedRefs = references.map(ref => (ref, unhideAst(ref)))

        // Need to unhide properties that were used during the query
        def replaceProps(ast: Ast) =
          BetaReduction(ast, TypeBehavior.ReplaceWithReduction, replacedRefs: _*) // Since properties could not actually be inside, don't typecheck the reduction
        def replacePropsOption(ast: Option[Ast]) =
          ast.map(replaceProps(_))

        q.copy(
          // Remove uneeded aliases, also remove all aliases on top level since they are not needed
          // (i.e. since quill uses positional indexes to do encoding)
          select = select,
          from = from,
          where = replacePropsOption(where),
          groupBy = replacePropsOption(groupBy),
          orderBy = orderBy.map(ob => ob.copy(ast = replaceProps(ob.ast))),
          limit = replacePropsOption(limit),
          offset = replacePropsOption(offset)
        )(q.quat)

    }

  def unhideAst(ast: Ast): Ast =
    Transform(ast) {
      case Property.Opinionated(a, n, r, v) =>
        Property.Opinionated(unhideAst(a), n, r, Visible)
    }

  private def expandContext(s: FromContext, asts: List[Ast]): (FromContext, LinkedHashSet[Property]) =
    s match {
      case QueryContext(q, alias) =>
        val refs = references(alias, asts)
        val reapplied = apply(q, refs)
        val filtered =
          reapplied match {
            case q: FlattenSqlQuery =>
              val filteredSelect = filterUnused(q.select, refs)
              expandNested(q.copy(select = filteredSelect)(q.quat), false)
            case SetOperationSqlQuery(a, op, b) =>
              SetOperationSqlQuery(apply(a, refs), op, apply(b, refs))(q.quat)
            case UnaryOperationSqlQuery(op, q) =>
              UnaryOperationSqlQuery(op, apply(q, refs))(q.quat)
          }
        (QueryContext(filtered, alias), refs)
      case JoinContext(t, a, b, on) =>
        val (left, leftRefs) = expandContext(a, asts :+ on)
        val (right, rightRefs) = expandContext(b, asts :+ on)
        (JoinContext(t, left, right, on), leftRefs ++ rightRefs)
      case FlatJoinContext(t, a, on) =>
        val (next, refs) = expandContext(a, asts :+ on)
        (FlatJoinContext(t, next, on), refs)
      case _: TableContext | _: InfixContext => (s, new mutable.LinkedHashSet[Property]())
    }

  private def references(alias: String, asts: List[Ast]) =
    LinkedHashSet.empty ++ (References(State(Ident(alias, Quat.Value), Nil))(asts)(_.apply)._2.state.references)
}

case class State(ident: Ident, references: List[Property])

case class References(val state: State)
  extends StatefulTransformer[State] {

  import state._

  override def apply(a: Ast) =
    a match {
      case `reference`(p) => (p, References(State(ident, references :+ p)))
      case other          => super.apply(a)
    }

  object reference {
    def unapply(p: Property): Option[Property] =
      p match {
        case Property(`ident`, name)      => Some(p)
        case Property(reference(_), name) => Some(p)
        case other                        => None
      }
  }
}

