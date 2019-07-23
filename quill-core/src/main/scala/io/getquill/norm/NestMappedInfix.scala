package io.getquill.norm

import io.getquill.ast._

object NestMappedInfix extends StatelessTransformer {

  def hasInfix(asts: Ast*): Boolean =
    asts.exists(ast => CollectAst.byType[Infix](ast).nonEmpty)

  override def apply(ast: Ast): Ast =
    ast match {
      case m @ Map(_, x, cc @ CaseClass(values)) if hasInfix(cc) => //Nested(m)
        Map(Nested(m), x,
          CaseClass(values.map {
            case (str, _) => (str, Property(x, str))
          }))

      case m @ Map(_, x, tup @ Tuple(values)) if hasInfix(tup) =>
        Map(Nested(m), x,
          Tuple(values.zipWithIndex.map {
            case (_, i) => Property(x, s"_${i + 1}")
          }))

      case m @ Map(_, x, i @ Infix(_, _)) =>
        println("Infix Case")
        Map(Nested(m), x, Property(x, "_1"))

      case m @ Map(_, x, Property(prop, _)) if hasInfix(prop) =>
        println("Property Case")
        Map(Nested(m), x, Property(x, "_1"))

      case m @ Map(_, x, BinaryOperation(a, _, b)) if hasInfix(a, b) =>
        println("Binary Op Case")
        Map(Nested(m), x, Property(x, "_1"))

      case m @ Map(_, x, UnaryOperation(_, a)) if hasInfix(a) =>
        println("Unary Op Case")
        Map(Nested(m), x, Property(x, "_1"))

      case other => super.apply(other)
    }
}
