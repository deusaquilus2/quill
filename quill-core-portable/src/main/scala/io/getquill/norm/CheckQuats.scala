package io.getquill.norm

import io.getquill.ast.{ Ast, Quat, Query, StatelessTransformer }

case class CheckQuats(header: String) extends StatelessTransformer {

  override def apply(query: Query) =
    check(query)(super.apply(_))

  override def apply(ast: Ast): Ast =
    check(ast)(super.apply(_))

  protected def check[T <: Ast](ast: T)(continue: T => T): T = {
    ast.quat match {
      case Quat.Error(msg) =>
        throw new IllegalStateException(s"Failed Phase ${header}: ${msg}")
      case _ =>
        continue(ast) //super.apply(ast)
    }
  }
}
