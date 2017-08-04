package io.getquill.context.ndbc

import java.time.LocalDate
import java.time.LocalDateTime
import java.time.ZoneOffset
import java.util.Date

import scala.math.BigDecimal.javaBigDecimal2bigDecimal

import io.trane.ndbc.value.Value
import java.util.UUID

trait Decoders {
  this: NdbcContext[_, _] =>

  type Decoder[T] = BaseDecoder[T]

  protected val zoneOffset: ZoneOffset

  def decoder[T](f: Value[_] => T): Decoder[T] =
    (index, row) => f(row.column(index))

  implicit def mappedDecoder[I, O](implicit mapped: MappedEncoding[I, O], d: Decoder[I]): Decoder[O] =
    mappedBaseDecoder(mapped, d)

  implicit def optionDecoder[T](implicit d: Decoder[T]): Decoder[Option[T]] =
    (idx, row) =>
      row.column(idx) match {
        case Value.NULL => None
        case value => Option(d(idx, row))
      }

  implicit val uuidDecoder: Decoder[UUID] = decoder(_.getUUID)
  implicit val stringDecoder: Decoder[String] = decoder(_.getString)
  implicit val bigDecimalDecoder: Decoder[BigDecimal] = decoder(_.getBigDecimal)
  implicit val booleanDecoder: Decoder[Boolean] = decoder(_.getBoolean)
  implicit val byteDecoder: Decoder[Byte] = decoder(_.getByte)
  implicit val shortDecoder: Decoder[Short] = decoder(_.getShort)
  implicit val intDecoder: Decoder[Int] = decoder(_.getInteger)
  implicit val longDecoder: Decoder[Long] = decoder(_.getLong)
  implicit val floatDecoder: Decoder[Float] = decoder(_.getFloat)
  implicit val doubleDecoder: Decoder[Double] = decoder(_.getDouble)
  implicit val byteArrayDecoder: Decoder[Array[Byte]] = decoder(_.getByteArray)
  implicit val dateDecoder: Decoder[Date] = decoder(v => Date.from(v.getLocalDateTime.toInstant(zoneOffset)))
  implicit val localDateDecoder: Decoder[LocalDate] = decoder(_.getLocalDate)
  implicit val localDateTimeDecoder: Decoder[LocalDateTime] = decoder(_.getLocalDateTime)

  def arrayDecoder[T, Col <: Seq[T]](f: Value[_] => Array[T])(implicit bf: CBF[T, Col]) = decoder(v => bf().++=(f(v)).result())

  implicit def arrayStringDecoder[Col <: Seq[String]](implicit bf: CBF[String, Col]): Decoder[Col] = arrayDecoder(_.getStringArray)
  implicit def arrayBigDecimalDecoder[Col <: Seq[BigDecimal]](implicit bf: CBF[BigDecimal, Col]): Decoder[Col] = arrayDecoder(_.getBigDecimalArray.map(BigDecimal(_)))
  implicit def arrayBooleanDecoder[Col <: Seq[Boolean]](implicit bf: CBF[Boolean, Col]): Decoder[Col] = arrayDecoder(_.getBooleanArray.map(_.booleanValue))
  implicit def arrayByteDecoder[Col <: Seq[Byte]](implicit bf: CBF[Byte, Col]): Decoder[Col] = arrayDecoder(_.getByteArray)
  implicit def arrayShortDecoder[Col <: Seq[Short]](implicit bf: CBF[Short, Col]): Decoder[Col] = arrayDecoder(_.getShortArray.map(_.shortValue))
  implicit def arrayIntDecoder[Col <: Seq[Int]](implicit bf: CBF[Int, Col]): Decoder[Col] = arrayDecoder(_.getIntegerArray.map(_.intValue))
  implicit def arrayLongDecoder[Col <: Seq[Long]](implicit bf: CBF[Long, Col]): Decoder[Col] = arrayDecoder(_.getLongArray.map(_.longValue))
  implicit def arrayFloatDecoder[Col <: Seq[Float]](implicit bf: CBF[Float, Col]): Decoder[Col] = arrayDecoder(_.getFloatArray.map(_.floatValue))
  implicit def arrayDoubleDecoder[Col <: Seq[Double]](implicit bf: CBF[Double, Col]): Decoder[Col] = arrayDecoder(_.getDoubleArray.map(_.doubleValue))
  implicit def arrayDateDecoder[Col <: Seq[Date]](implicit bf: CBF[Date, Col]): Decoder[Col] = arrayDecoder(_.getLocalDateTimeArray.map(v => Date.from(v.toInstant(zoneOffset))))
  implicit def arrayLocalDateDecoder[Col <: Seq[LocalDate]](implicit bf: CBF[LocalDate, Col]): Decoder[Col] = arrayDecoder(_.getLocalDateArray)
}
