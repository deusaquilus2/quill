package io.getquill.quotation

import scala.reflect.macros.whitebox.Context
import io.getquill.ast._
import io.getquill.quat.Quat

import scala.reflect.api.Universe

trait QuatMaking extends QuatMakingBase {
  val c: Context
  type Uni = c.universe.type
  // NOTE: u needs to be lazy otherwise sets value from c before c can be initialized by higher level classes
  lazy val u: Uni = c.universe
}

object InferQuatRuntime extends QuatMakingBase {
  type Uni = scala.reflect.api.Universe
  lazy val u = scala.reflect.runtime.universe
  def of[T: u.TypeTag] = inferQuat(implicitly[u.TypeTag[T]].tpe)
}

trait QuatMakingBase {
  type Uni <: Universe
  val u: Uni
  import u.{ Ident => _, Constant => _, Function => _, If => _, Block => _, _ }

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
}
