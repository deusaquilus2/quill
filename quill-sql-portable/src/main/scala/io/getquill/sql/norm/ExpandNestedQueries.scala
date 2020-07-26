package io.getquill.context.sql.norm

import io.getquill.NamingStrategy
import io.getquill.ast.Ast
import io.getquill.ast.Ident
import io.getquill.ast._
import io.getquill.ast.StatefulTransformer
import io.getquill.ast.Visibility.{ Hidden, Visible }
import io.getquill.context.sql._

import scala.collection.mutable.LinkedHashSet
import io.getquill.util.Interpolator
import io.getquill.util.Messages.TraceType.NestedQueryExpansion
import io.getquill.context.sql.norm.nested.ExpandSelect
import io.getquill.norm.{ BetaReduction, PropertyMatroshka, TypeBehavior }
import io.getquill.quat.Quat

import scala.collection.mutable

class ExpandSelection(from: List[FromContext]) {

  private def refersToEntity(ast: Ast) = {
    val tables = from.collect { case TableContext(entity, alias) => alias }
    ast match {
      case Ident(v, _)                       => tables.contains(v)
      case PropertyMatroshka(Ident(v, _), _) => tables.contains(v)
      case _                                 => false
    }
  }

  def apply(values: List[SelectValue]): List[SelectValue] =
    values.flatMap(apply(_))

  def apply(value: SelectValue): List[SelectValue] = {
    value match {
      // Assuming there's no case class or tuple buried inside or a property i.e. if there were,
      // the beta reduction would have unrolled them already
      case SelectValue(ast @ PropertyOrTerminal(), alias, concat) =>
        val exp = expand(ast)
        exp.map {
          case (p: Property, path) =>
            SelectValue(p, Some(path.mkString), concat)
          case (other, _) =>
            SelectValue(other, None, concat)
        }
      case SelectValue(Tuple(values), alias, concat) =>
        values.zipWithIndex.flatMap {
          case (ast, i) =>
            apply(SelectValue(ast, alias, concat)).map { sv =>
              sv.copy(
                alias = sv.alias.orElse(Some(""))
                  .map(alias => s"_${i + 1}${alias}")
              )
            }
        }
      case SelectValue(CaseClass(fields), alias, concat) =>
        fields.flatMap {
          case (name, ast) =>
            apply(SelectValue(ast, alias, concat)).map { sv =>
              sv.copy(
                alias = sv.alias.orElse(Some(""))
                  .map(alias => s"${name}${alias}")
              )
            }
        }
      // Direct infix select, etc...
      case other => List(other)
    }
  }

  object PropertyOrTerminal {
    def unapply(ast: Ast): Boolean =
      Terminal.unapply(ast) || ast.isInstanceOf[Property]
  }

  object Terminal {
    def unapply(ast: Ast): Boolean =
      ast.isInstanceOf[Ident] || ast.isInstanceOf[Infix] || ast.isInstanceOf[Constant]
  }

  def expand(ast: Ast): List[(Ast, List[String])] = {
    def unhideProps(p: Ast): Ast =
      p match {
        case Property.Opinionated(ast, name, r, v) =>
          Property.Opinionated(unhideProps(ast), name, r, Visible)
        case other =>
          other
      }

    ast match {
      case id @ Terminal() =>
        val isEntity = refersToEntity(id)
        id.quat match {
          case p: Quat.Product => QuatExpander(isEntity)(p, id)
          case _               => List(id).map(p => (p, List.empty))
        }
      // Assuming a property contains only an Ident, Infix or Constant at this point
      // and all situations where there is a case-class, tuple, etc... inside have already been beta-reduced
      case prop @ PropertyMatroshka(id @ Terminal(), _) =>
        val isEntity = refersToEntity(id)
        val propsWithVisibility = if (!isEntity) unhideProps(prop) else prop
        prop.quat match {
          case p: Quat.Product => QuatExpander(isEntity)(p, propsWithVisibility)
          case _               => List(propsWithVisibility).map(p => (p, List.empty))
        }
      case other => List(other).map(p => (p, List.empty))
    }
  }

  /* Take a quat and project it out as nested properties with some core ast inside.
   * quat: CC(foo,bar:Quat(a,b)) with core id:Ident(x) =>
   *   List( Prop(id,foo) [foo], Prop(Prop(id,bar),a) [bar.a], Prop(Prop(id,bar),b) [bar.b] )
   */
  case class QuatExpander(refersToEntity: Boolean) {
    def apply(quat: Quat.Product, core: Ast): List[(Property, List[String])] =
      applyInner(quat, core)

    def applyInner(quat: Quat.Product, core: Ast): List[(Property, List[String])] = {
      // Property (and alias path) should be visible unless we are referring directly to a TableContext
      // with an Entity that has embedded fields. In that case, only top levels should show since
      // we're selecting from an actual table and in that case, the embedded paths don't actually exist.
      val wholePathVisible = !refersToEntity

      quat.fields.flatMap {
        case (name, child: Quat.Product) =>
          applyInner(child, Property.Opinionated(core, name, Renameable.ByStrategy, if (wholePathVisible) Visible else Hidden)).map { // TODO Need to know if renames have been applied in order to create as fixed vs renameable, in RenameProperties keep that information
            case (prop, path) =>
              (prop, name +: path)
          }
        case (name, _) =>
          // The innermost entity of the quat. This is always visible since it is the actual column of the table
          List((Property.Opinionated(core, name, Renameable.ByStrategy, Visible), List(name)))
      }.toList
    }
  }

}

class ExpandNestedQueries2(foo: Any) {

  val interp = new Interpolator(NestedQueryExpansion, 3)
  import interp._

  def apply(q: SqlQuery): SqlQuery = {
    apply(q, true)
  }

  private def apply(q: SqlQuery, isTopLevel: Boolean = false): SqlQuery =
    q match {
      case q: FlattenSqlQuery =>
        val expand = expandNested(q.copy(select = new ExpandSelection(q.from)(q.select))(q.quat), isTopLevel)
        trace"Expanded Nested Query $q into $expand".andLog()
        expand
      case SetOperationSqlQuery(a, op, b) =>
        SetOperationSqlQuery(apply(a), op, apply(b))(q.quat)
      case UnaryOperationSqlQuery(op, q) =>
        UnaryOperationSqlQuery(op, apply(q))(q.quat)
    }

  private def expandNested(q: FlattenSqlQuery, isTopLevel: Boolean): SqlQuery =
    q match {
      case FlattenSqlQuery(from, where, groupBy, orderBy, limit, offset, select, distinct) =>

        val newFroms = q.from.map(expandContext(_))

        def distinctIfNotTopLevel(values: List[SelectValue]) =
          if (isTopLevel)
            values
          else
            values.distinct

        /*
         * In sub-queries, need to make sure that the same field/alias pair is not selected twice
         * which is possible when aliases are used. For example, something like this:
         *
         * case class Emb(id: Int, name: String) extends Embedded
         * case class Parent(id: Int, name: String, emb: Emb) extends Embedded
         * case class GrandParent(id: Int, par: Parent)
         * val q = quote { query[GrandParent].map(g => g.par).distinct.map(p => (p.name, p.emb, p.id, p.emb.id)).distinct.map(tup => (tup._1, tup._2, tup._3, tup._4)).distinct }
         * Will cause double-select inside the innermost subselect:
         * SELECT DISTINCT theParentName AS theParentName, id AS embid, theName AS embtheName, id AS id, id AS embid FROM GrandParent g
         * Note how embid occurs twice? That's because (p.emb.id, p.emb) are expanded into (p.emb.id, p.emb.id, e.emb.name).
         *
         * On the other hand if the query is top level we need to make sure not to do this deduping or else the encoders won't work since they rely on clause positions
         * For example, something like this:
         * val q = quote { query[GrandParent].map(g => g.par).distinct.map(p => (p.name, p.emb, p.id, p.emb.id)) }
         * Would normally expand to this:
         * SELECT p.theParentName, p.embid, p.embtheName, p.id, p.embid FROM ...
         * Note now embed occurs twice? We need to maintain this because the second element of the output tuple
         * (p.name, p.emb, p.id, p.emb.id) needs the fields p.embid, p.embtheName in that precise order in the selection
         * or they cannot be encoded.
         */
        val newSelects =
          distinctIfNotTopLevel(select)

        q.copy(select = newSelects, from = newFroms)(q.quat)
    }

  def expandContext(s: FromContext): FromContext =
    s match {
      case QueryContext(q, alias) =>
        QueryContext(apply(q), alias)
      case JoinContext(t, a, b, on) =>
        val left = expandContext(a)
        val right = expandContext(b)
        JoinContext(t, left, right, on)
      case FlatJoinContext(t, a, on) =>
        val next = expandContext(a)
        FlatJoinContext(t, next, on)
      case _: TableContext | _: InfixContext => s
    }

}

class ExpandNestedQueries(strategy: NamingStrategy) {

  val interp = new Interpolator(NestedQueryExpansion, 3)
  import interp._

  def apply(q: SqlQuery, references: List[Property]): SqlQuery =
    apply(q, LinkedHashSet.empty ++ references, true)

  // Using LinkedHashSet despite the fact that it is mutable because it has better characteristics then ListSet.
  // Also this collection is strictly internal to ExpandNestedQueries and exposed anywhere else.
  private def apply(q: SqlQuery, references: LinkedHashSet[Property], isTopLevel: Boolean = false): SqlQuery =
    q match {
      case q: FlattenSqlQuery =>
        val expand = expandNested(q.copy(select = ExpandSelect(q.select, references, strategy))(q.quat), isTopLevel)
        trace"Expanded Nested Query $q into $expand".andLog()
        expand
      case SetOperationSqlQuery(a, op, b) =>
        SetOperationSqlQuery(apply(a, references), op, apply(b, references))(q.quat)
      case UnaryOperationSqlQuery(op, q) =>
        UnaryOperationSqlQuery(op, apply(q, references))(q.quat)
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

        def distinctIfNotTopLevel(values: List[SelectValue]) =
          if (isTopLevel)
            values
          else
            values.distinct

        /*
         * In sub-queries, need to make sure that the same field/alias pair is not selected twice
         * which is possible when aliases are used. For example, something like this:
         *
         * case class Emb(id: Int, name: String) extends Embedded
         * case class Parent(id: Int, name: String, emb: Emb) extends Embedded
         * case class GrandParent(id: Int, par: Parent)
         * val q = quote { query[GrandParent].map(g => g.par).distinct.map(p => (p.name, p.emb, p.id, p.emb.id)).distinct.map(tup => (tup._1, tup._2, tup._3, tup._4)).distinct }
         * Will cause double-select inside the innermost subselect:
         * SELECT DISTINCT theParentName AS theParentName, id AS embid, theName AS embtheName, id AS id, id AS embid FROM GrandParent g
         * Note how embid occurs twice? That's because (p.emb.id, p.emb) are expanded into (p.emb.id, p.emb.id, e.emb.name).
         *
         * On the other hand if the query is top level we need to make sure not to do this deduping or else the encoders won't work since they rely on clause positions
         * For example, something like this:
         * val q = quote { query[GrandParent].map(g => g.par).distinct.map(p => (p.name, p.emb, p.id, p.emb.id)) }
         * Would normally expand to this:
         * SELECT p.theParentName, p.embid, p.embtheName, p.id, p.embid FROM ...
         * Note now embed occurs twice? We need to maintain this because the second element of the output tuple
         * (p.name, p.emb, p.id, p.emb.id) needs the fields p.embid, p.embtheName in that precise order in the selection
         * or they cannot be encoded.
         */
        val newSelects =
          distinctIfNotTopLevel(select.map(sv => sv.copy(ast = replaceProps(sv.ast))))

        q.copy(
          select = newSelects,
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

  private def unhideProperties(sv: SelectValue) =
    sv.copy(ast = unhideAst(sv.ast))

  private def expandContext(s: FromContext, asts: List[Ast]): (FromContext, LinkedHashSet[Property]) =
    s match {
      case QueryContext(q, alias) =>
        val refs = references(alias, asts)
        (QueryContext(apply(q, refs), alias), refs)
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
    LinkedHashSet.empty ++ (References(State(Ident(alias, Quat.Value), Nil))(asts)(_.apply)._2.state.references) // TODO scrap this whole thing with quats
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
