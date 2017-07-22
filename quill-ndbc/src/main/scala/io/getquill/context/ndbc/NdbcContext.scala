package io.getquill.context.ndbc

import java.util.HashMap

import scala.annotation.tailrec
import scala.util.Try

import org.slf4j.LoggerFactory

import com.typesafe.scalalogging.Logger

import io.getquill.NamingStrategy
import io.getquill.context.sql.SqlContext
import io.getquill.context.sql.idiom.SqlIdiom
import io.trane.future.scala.Future
import io.trane.future.scala._
import io.trane.ndbc.DataSource
import io.trane.ndbc.PreparedStatement
import io.trane.ndbc.Row
import io.trane.ndbc.value.LongValue
import java.time.ZoneOffset

abstract class NdbcContext[Dialect <: SqlIdiom, Naming <: NamingStrategy](dataSource: DataSource)
    extends SqlContext[Dialect, Naming]
    with Encoders
    with Decoders {

  protected val zoneOffset: ZoneOffset = ZoneOffset.UTC

  private val logger: Logger =
    Logger(LoggerFactory.getLogger(classOf[NdbcContext[_, _]]))

  override type PrepareRow = PreparedStatement
  override type ResultRow = Row

  override type RunQueryResult[T] = Future[List[T]]
  override type RunQuerySingleResult[T] = Future[T]
  override type RunActionResult = Future[Long]
  override type RunActionReturningResult[T] = Future[T]
  override type RunBatchActionResult = Future[List[Long]]
  override type RunBatchActionReturningResult[T] = Future[List[T]]

  def close() = {
    dataSource.close()
    ()
  }

  def probe(sql: String) =
    Try(dataSource.query(sql))

  def transaction[T](f: => Future[T]): Future[T] =
    dataSource.transactional(() => f.toJava).toScala

  def executeQuery[T](sql: String, prepare: PreparedStatement => PreparedStatement = identity, extractor: Row => T = identity[Row] _): Future[List[T]] = {
    val ps = prepare(PreparedStatement.apply(sql))
    logger.debug(ps.toString())
    dataSource.query(ps).toScala.map { rs =>
      extractResult(rs.iterator, extractor)
    }
  }

  def executeQuerySingle[T](sql: String, prepare: PreparedStatement => PreparedStatement = identity, extractor: Row => T = identity[Row] _): Future[T] =
    executeQuery(sql, prepare, extractor).map(handleSingleResult(_))

  def executeAction[T](sql: String, prepare: PreparedStatement => PreparedStatement = identity): Future[Long] = {
    val ps = prepare(PreparedStatement.apply(sql))
    logger.debug(ps.toString())
    dataSource.execute(ps).toScala.map(_.longValue())
  }

  def executeActionReturning[O](sql: String, prepare: PreparedStatement => PreparedStatement = identity, extractor: Row => O, returningColumn: String): Future[O] =
    executeAction(sql, prepare).map { id =>
      extractor(Row.apply(new HashMap, Array(new LongValue(id))))
    }

  def executeBatchAction(groups: List[BatchGroup]): Future[List[Long]] =
    Future.sequence {
      groups.map {
        case BatchGroup(sql, prepare) =>
          prepare.foldLeft(Future.successful(List.empty[Long])) {
            case (acc, prepare) =>
              acc.flatMap { list =>
                executeAction(sql, prepare).map(list :+ _)
              }
          }
      }
    }.map(_.flatten.toList)

  def executeBatchActionReturning[T](groups: List[BatchGroupReturning], extractor: Row => T): Future[List[T]] =
    Future.sequence {
      groups.map {
        case BatchGroupReturning(sql, column, prepare) =>
          prepare.foldLeft(Future.successful(List.empty[T])) {
            case (acc, prepare) =>
              acc.flatMap { list =>
                executeActionReturning(sql, prepare, extractor, column).map(list :+ _)
              }
          }
      }
    }.map(_.flatten.toList)

  @tailrec
  private def extractResult[T](rs: java.util.Iterator[Row], extractor: Row => T, acc: List[T] = List()): List[T] =
    if (rs.hasNext)
      extractResult(rs, extractor, extractor(rs.next()) :: acc)
    else
      acc.reverse
}
