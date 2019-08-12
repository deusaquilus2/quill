package io.getquill.norm

import io.getquill.Spec
import io.getquill.testContext._
import org.scalactic.Equality

class NormalizeAggregationIdentSpec extends Spec {

  // TODO Back here

  implicit def astEq[T <: io.getquill.ast.Ast](implicit tt: scala.reflect.runtime.universe.TypeTag[T]) =
    new Equality[T] {
      def areEqual(a: T, b: Any): Boolean =
        b match {
          case p: io.getquill.ast.Ast => p.neutralize == a.neutralize
          case _                      => false
        }
    }

  "multiple select" in {
    val q = quote {
      qr1.groupBy(p => p.i).map {
        case (i, qrs) => i -> qrs.map(_.l).sum
      }
    }
    val n = quote {
      qr1.groupBy(p => p.i).map {
        p => p._1 -> p._2.map(p => p.l).sum
      }
    }
    (Normalize(q.ast) mustEqual (n.ast))(astEq)
  }
}
