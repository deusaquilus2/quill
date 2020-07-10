package io.getquill.norm

import io.getquill.ast.{ Filter, FlatMap, Query, Union, UnionAll }

object SymbolicReduction {

  def unapply(q: Query) =
    q match {

      // bottles.filter(bottle => isMerlot).flatMap(merlotBottle => {withCheese})
      //     bottles.flatMap(merlotBottle => {withCheese}.filter(_ => isMerlot[bottle := merlotBottle]))

      // For example:
      //   withCheese is cheeses.filter(cheese => cheese.pairsWith == merlotBottle)
      //   isMerlot is bottle.isMerlot
      //
      // bottles.filter(bottle => bottle.isMerlot).flatMap(merlotBottle => {cheeses.filter(cheese => cheese.pairsWith == merlotBottle)} )
      //     bottles.flatMap(merlotBottle => cheeses.filter({bottle.isMerlot}[bottle := merlotBottle]).filter(cheese => cheese.pairsWith == merlotBottle)}
      // which is:
      //     bottles.flatMap(merlotBottle => cheeses.filter({doesnt-matter} => merlotBottle.isMerlot).filter(cheese => cheese.pairsWith == merlotBottle)

      // a.filter(b => c).flatMap(d => e.$) =>
      //     a.flatMap(d => e.filter(_ => c[b := d]).$)
      case FlatMap(Filter(a, b, c), d, e: Query) =>
        val cr = BetaReduction(c, b -> d)
        val er = AttachToEntity(Filter(_, _, cr))(e)
        Some(FlatMap(a, d, er))

      // a.flatMap(b => c).flatMap(d => e) =>
      //     a.flatMap(b => c.flatMap(d => e))
      case FlatMap(FlatMap(a, b, c), d, e) =>
        Some(FlatMap(a, b, FlatMap(c, d, e)))

      // a.union(b).flatMap(c => d)
      //      a.flatMap(c => d).union(b.flatMap(c => d))
      case FlatMap(Union(a, b), c, d) =>
        Some(Union(FlatMap(a, c, d), FlatMap(b, c, d)))

      // a.unionAll(b).flatMap(c => d)
      //      a.flatMap(c => d).unionAll(b.flatMap(c => d))
      case FlatMap(UnionAll(a, b), c, d) =>
        Some(UnionAll(FlatMap(a, c, d), FlatMap(b, c, d)))

      case other => None
    }
}
