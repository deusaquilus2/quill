package io.getquill.sql.norm

import io.getquill.NamingStrategy
import io.getquill.ast.Property
import io.getquill.context.sql.{ FlattenSqlQuery, SelectValue }

/**
 * Remove aliases at the top level of the AST since they are not needed
 * (quill uses select row indexes to figure out what data corresponds to what encodeable object)
 * as well as entities whose aliases are the same as their selection e.g. "select x.foo as foo"
 * since this just adds syntactic noise.
 */
case class RemoveExtraAlias(strategy: NamingStrategy) extends StatelessQueryTransformer {
  // Remove aliases that are the same as as the select values. Since a strategy may change the name,
  // use a heuristic where if the column naming strategy make the property name be different from the
  // alias, keep the column property name.
  def strategyMayChangeColumnName(column: String): Boolean =
    strategy.column(column) != column || strategy.default(column) != column

  private def removeUnneededAlias(value: SelectValue): SelectValue =
    value match {
      // Can remove an alias if the alias is equal to the property name and the property name cannot be changed but the naming strategy
      case sv @ SelectValue(p: Property, Some(alias), _) if !strategyMayChangeColumnName(p.name) && p.name == alias =>
        sv.copy(alias = None)
      case _ =>
        value
    }

  override protected def expandNested(q: FlattenSqlQuery, isTopLevel: Boolean): FlattenSqlQuery = {
    val from = q.from.map(expandContext(_))
    val select =
      q.select
        .map(removeUnneededAlias(_))
        .map { sv =>
          if (isTopLevel)
            sv.copy(alias = None)
          else
            sv
        }
    q.copy(select = select, from = from)(q.quat)
  }
}
