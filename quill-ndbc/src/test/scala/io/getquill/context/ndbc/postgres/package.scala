package io.getquill.context.ndbc

import io.getquill._
import io.getquill.context.sql.{ TestDecoders, TestEncoders }

package object postgres {

  object testContext extends PostgresNdbcContext[Literal]("testPostgresDB") with TestEntities with TestEncoders with TestDecoders

}
