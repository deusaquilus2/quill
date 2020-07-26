package io.getquill.sql.norm

import io.getquill.ast.Property
import io.getquill.context.sql.{ FlattenSqlQuery, SelectValue }

/**
 * Remove aliases at the top level of the AST since they are not needed
 * (quill uses select row indexes to figure out what data corresponds to what encodeable object)
 * as well as entities whose aliases are the same as their selection e.g. "select x.foo as foo"
 * since this just adds syntactic noise.
 */
object RemoveExtraAlias extends StatelessQueryTransformer {
  // Remove aliases that are the same as as the select values
  private def removeUnneededAlias(value: SelectValue): SelectValue =
    value match {
      case sv @ SelectValue(p: Property, Some(alias), _) if (p.name == alias) =>
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
