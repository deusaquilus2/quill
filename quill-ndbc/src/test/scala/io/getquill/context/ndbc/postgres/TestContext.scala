package io.getquill.context.ndbc.postgres

import io.getquill.context.sql.{ TestDecoders, TestEncoders }
import io.getquill.{ Literal, TestEntities }

import scala.concurrent.{ Await, Future }
import scala.concurrent.duration.Duration
import io.getquill.PostgresNdbcContext

class TestContext extends PostgresNdbcContext[Literal]("testPostgresDB")
  with TestEntities
  with TestEncoders
  with TestDecoders {

  def await[T](f: Future[T]): T = Await.result(f, Duration.Inf)
}
