package io.getquill.sql.norm

import io.getquill.ast.{ Ast, CollectAst, Ident, Property, StatefulTransformer }
import io.getquill.context.sql.{ FlatJoinContext, FlattenSqlQuery, FromContext, InfixContext, JoinContext, QueryContext, SelectValue, SetOperationSqlQuery, SqlQuery, TableContext, UnaryOperationSqlQuery }
import io.getquill.norm.PropertyMatroshka
import io.getquill.quat.Quat

import scala.collection.mutable
import scala.collection.mutable.LinkedHashSet

/**
 * Filter out unused subquery properties. This is safe to do after `ExpandNestedQueries`
 * now since all properties have been propagated from quats from parent to child
 * SQL select trees.
 */
object RefineSubqueryProperties {

  def apply(q: SqlQuery): SqlQuery =
    apply(q, LinkedHashSet.empty, true)

  private def apply(q: SqlQuery, references: LinkedHashSet[Property], isTopLevel: Boolean = false): SqlQuery =
    q match {
      case q: FlattenSqlQuery =>
        // gather asts used here
        val asts = gatherAsts(q)

        // recurse into the from clause with ExpandContext
        val fromContextsAndSuperProps = q.from.map(expandContext(_, asts))
        val fromContexts = fromContextsAndSuperProps.map(_._1)

        if (!isTopLevel) {
          // copy the new from clause and filter aliases
          val select = filterUnused(q.select, references.toSet)
          q.copy(from = fromContexts, select = select)(q.quat)
        } else {
          // If we are on the top level, the list of aliases being used by clauses outer to 'us'
          // don't exist since we are the outermost level of the sql. Therefore no filteration
          // should happen in that case.
          q
        }

      case SetOperationSqlQuery(a, op, b) =>
        SetOperationSqlQuery(apply(a, references), op, apply(b, references))(q.quat)
      case UnaryOperationSqlQuery(op, q) =>
        UnaryOperationSqlQuery(op, apply(q, references))(q.quat)
    }

  private def filterUnused(select: List[SelectValue], references: Set[Property]): List[SelectValue] = {
    val usedAliases = references.map {
      case PropertyMatroshka(_, list) => list.mkString
    }.toSet
    select.filter(sv =>
      sv.alias.forall(aliasValue => usedAliases.contains(aliasValue)) ||
        hasImpureInfix(sv.ast))
  }

  private def hasImpureInfix(ast: Ast) =
    CollectAst.byType[io.getquill.ast.Infix](ast).find(i => !i.pure).isDefined

  private def gatherAsts(q: FlattenSqlQuery): List[Ast] =
    q match {
      case FlattenSqlQuery(from, where, groupBy, orderBy, limit, offset, select, distinct) =>
        Nil ++ select.map(_.ast) ++ where ++ groupBy ++ orderBy.map(_.ast) ++ limit ++ offset
    }

  private def expandContext(s: FromContext, asts: List[Ast]): (FromContext, LinkedHashSet[Property]) =
    s match {
      case QueryContext(q, alias) =>
        val refs = references(alias, asts)
        val reapplied = apply(q, refs)
        (QueryContext(reapplied, alias), refs)
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

