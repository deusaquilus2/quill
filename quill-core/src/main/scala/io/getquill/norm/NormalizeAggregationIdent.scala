package io.getquill.norm

import io.getquill.ast._

object NormalizeAggregationIdent {

  def unapply(q: Query) =
    q match {

      // a => a.b.map(x => x.c).agg =>
      //   a => a.b.map(a => a.c).agg
      case Aggregation(op, Map(p @ Property(i: Ident, _, _), mi, Property(_: Ident, n, renameable))) if i != mi =>
        Some(Aggregation(op, Map(p, i, Property(i, n, renameable)))) // in example aove, if c in x.c is fixed c in a.c should also be

      case _ => None
    }
}
