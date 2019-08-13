package io.getquill

import io.getquill.ast.Renameable.Internal
import io.getquill.ast.{ Ast, Property, Transform }
import org.scalatest.BeforeAndAfterAll
import org.scalatest.FreeSpec
import org.scalatest.MustMatchers

import scala.concurrent.{ Await, Future }
import scala.concurrent.duration.Duration

abstract class Spec extends FreeSpec with MustMatchers with BeforeAndAfterAll {
  def await[T](f: Future[T]): T = Await.result(f, Duration.Inf)

  def setTuplePropsInternal(ast: Ast) =
    Transform(ast) {
      case Property(ast, name, _) if (name.matches("_[0-9]*")) => Property(ast, name, Internal)
    }
}
