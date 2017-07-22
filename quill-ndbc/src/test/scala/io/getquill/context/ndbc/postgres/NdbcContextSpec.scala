//package io.getquill.context.ndbc.postgres
//
//import scala.concurrent.Await
//import io.trane.future.scala.Future
//import scala.concurrent.duration.Duration
//
//import io.getquill.Spec
//
//class MysqlAsyncContextSpec extends Spec {
//
//  import testContext._
//
//  def await[T](f: Future[T]) = Await.result(f, Duration.Inf)
//
//  "runs non-batched action" in {
//    val insert = quote { (i: Int) =>
//      qr1.insert(_.i -> i)
//    }
//    await(testContext.run(insert(lift(1)))) mustEqual 1
//  }
//}
