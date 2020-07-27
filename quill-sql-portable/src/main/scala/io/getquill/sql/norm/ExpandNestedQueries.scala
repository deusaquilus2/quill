package io.getquill.context.sql.norm

import io.getquill.ast._
import io.getquill.context.sql._
import io.getquill.sql.norm.{ SelectPropertyExpander, StatelessQueryTransformer }
import io.getquill.ast.PropertyOrCore

class ExpandSelection(from: List[FromContext]) {

  def apply(values: List[SelectValue]): List[SelectValue] =
    values.flatMap(apply(_))

  private def apply(value: SelectValue): List[SelectValue] = {
    value match {
      // Assuming there's no case class or tuple buried inside or a property i.e. if there were,
      // the beta reduction would have unrolled them already
      case SelectValue(ast @ PropertyOrCore(), alias, concat) =>
        val exp = SelectPropertyExpander(from)(ast)
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
}

object ExpandNestedQueries extends StatelessQueryTransformer {

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
