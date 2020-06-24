package io.getquill.quat

import io.getquill.dsl.QuotationDsl

import scala.annotation.tailrec
import scala.reflect.api.Universe
import scala.reflect.macros.whitebox.Context

trait QuatMaking extends QuatMakingBase {
  val c: Context
  type Uni = c.universe.type
  // NOTE: u needs to be lazy otherwise sets value from c before c can be initialized by higher level classes
  lazy val u: Uni = c.universe
}

object MakeQuat extends MakeQuat

trait MakeQuat extends QuatMakingBase {
  type Uni = scala.reflect.api.Universe
  lazy val u = scala.reflect.runtime.universe
  def of[T: u.TypeTag] = inferQuat(implicitly[u.TypeTag[T]].tpe)
}

trait QuatMakingBase {
  type Uni <: Universe
  val u: Uni
  import u.{ Block => _, Constant => _, Function => _, Ident => _, If => _, _ }

  def inferQuat(tpe: Type): Quat = {

    //case TypeRef(_, cls, _)) =>

    def caseClassConstructorArgs(tpe: Type) = {
      val constructor =
        tpe.members.collect {
          case m: MethodSymbol if m.isPrimaryConstructor => m
        }.head

      // TODO Quat Only one constructor param list supported so far? Have an error for that?
      constructor.paramLists(0).map { param =>
        (param.name.toString, param.typeSignature.asSeenFrom(tpe, tpe.typeSymbol))
      }
    }

    object CaseClassBaseType {
      def unapply(tpe: Type): Option[(String, List[(String, Type)])] =
        if (tpe.widen.typeSymbol.isClass && tpe.widen.typeSymbol.asClass.isCaseClass)
          Some((tpe.widen.typeSymbol.name.toString, caseClassConstructorArgs(tpe.widen)))
        else
          None
    }

    def parseType(tpe: Type): Quat =
      tpe match {
        case _ if (isNone(tpe)) =>
          Quat.Null
        case _ if (isOptionType(tpe)) =>
          val innerParam = innerOptionParam(tpe, None)
          parseType(innerParam)
        // For tuples
        case CaseClassBaseType(name, fields) if (name.startsWith("scala.Tuple")) =>
          Quat.Tuple(fields.map { case (_, fieldType) => parseType(fieldType) })
        // For other types of case classes
        case CaseClassBaseType(name, fields) =>
          Quat.Product(fields.map { case (fieldName, fieldType) => (fieldName, parseType(fieldType)) })
        // Otherwise it's a terminal value
        case _ =>
          Quat.Value
      }

    parseType(tpe)
  }

  object QuotedType {
    def unapply(tpe: Type) =
      paramOf[QuotationDsl#Quoted[Any]](tpe)
  }

  object QueryType {
    def unapply(tpe: Type) =
      paramOf[io.getquill.Query[Any]](tpe)
  }

  def paramOf[T](tpe: Type, maxDepth: Int = 100)(implicit tt: TypeTag[T]): Option[Type] = tpe match {
    case _ if (maxDepth == 0) =>
      throw new IllegalArgumentException("Max Depth")
    case _ if (!(tpe <:< tt.tpe)) =>
      None
    case TypeRef(_, cls, List(arg)) =>
      Some(arg)
    case _ =>
      val base = tpe.baseType(implicitly[TypeTag[T]].tpe.typeSymbol)
      paramOf(base, maxDepth - 1)
  }

  @tailrec
  private[getquill] final def innerOptionParam(tpe: Type, maxDepth: Option[Int]): Type = tpe match {
    // If it's a ref-type and an Option, pull out the argument
    case TypeRef(_, cls, List(arg)) if (cls.isClass && cls.asClass.fullName == "scala.Option") && maxDepth.forall(_ > 0) =>
      innerOptionParam(arg, maxDepth.map(_ - 1))
    // If it's not a ref-type but an Option, convert to a ref-type and reprocess
    // also since Nothing is a subtype of everything need to know to stop searching once Nothing
    // has been reached (since we have not gone inside anything, do not decrement the depth here).
    case _ if (isOptionType(tpe) && !(tpe =:= typeOf[Nothing])) && maxDepth.forall(_ > 0) =>
      innerOptionParam(tpe.baseType(typeOf[Option[Any]].typeSymbol), maxDepth)
    // Otherwise we have gotten to the actual type inside the nesting. Check what it is.
    case other => other
  }

  def isNone(tpe: Type) = {
    val era = tpe.erasure
    era =:= typeOf[None.type]
  }

  // Note. Used in other places beside here where None needs to be included in option type.
  def isOptionType(tpe: Type) = {
    val era = tpe.erasure
    era =:= typeOf[Option[Any]] || era =:= typeOf[Some[Any]] || era =:= typeOf[None.type]
  }
}
