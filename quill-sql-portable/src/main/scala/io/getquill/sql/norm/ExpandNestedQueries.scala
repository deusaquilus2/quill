package io.getquill.context.sql.norm

import io.getquill.ast.Ast
import io.getquill.ast.Ident
import io.getquill.ast._
import io.getquill.ast.Visibility.{ Hidden, Visible }
import io.getquill.context.sql._

import io.getquill.norm.PropertyMatroshka
import io.getquill.quat.Quat
import io.getquill.sql.norm.StatelessQueryTransformer

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

  private def apply(value: SelectValue): List[SelectValue] = {
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

      // Assuming renames have been applied so the value of a renamed field will be the 2nd element
      def isPropertyRenameable(name: String) =
        if (quat.renames.find(_._2 == name).isDefined)
          Renameable.Fixed
        else
          Renameable.ByStrategy

      quat.fields.flatMap {
        case (name, child: Quat.Product) =>
          applyInner(child, Property.Opinionated(core, name, isPropertyRenameable(name), if (wholePathVisible) Visible else Hidden)).map { // TODO Need to know if renames have been applied in order to create as fixed vs renameable, in RenameProperties keep that information
            case (prop, path) =>
              (prop, name +: path)
          }
        case (name, _) =>
          // The innermost entity of the quat. This is always visible since it is the actual column of the table
          List((Property.Opinionated(core, name, isPropertyRenameable(name), Visible), List(name)))
      }.toList
    }
  }

}

object ExpandNestedQueries2 extends StatelessQueryTransformer {

  protected override def apply(q: SqlQuery, isTopLevel: Boolean = false): SqlQuery =
    q match {
      case q: FlattenSqlQuery =>
        expandNested(q.copy(select = new ExpandSelection(q.from)(q.select))(q.quat), isTopLevel)
      case other =>
        super.apply(q, isTopLevel)
    }

  protected override def expandNested(q: FlattenSqlQuery, isTopLevel: Boolean): FlattenSqlQuery =
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
}
