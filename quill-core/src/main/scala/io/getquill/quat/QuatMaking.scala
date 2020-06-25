package io.getquill.quat

import io.getquill.dsl.QuotationDsl
import io.getquill.quat
import io.getquill.util.{ Messages, OptionalTypecheck }

import scala.annotation.tailrec
import scala.reflect.api.Universe
import scala.reflect.macros.whitebox.Context

trait QuatMaking extends QuatMakingBase {
  val c: Context
  type Uni = c.universe.type
  // NOTE: u needs to be lazy otherwise sets value from c before c can be initialized by higher level classes
  lazy val u: Uni = c.universe

  import u.{ Block => _, Constant => _, Function => _, Ident => _, If => _, _ }

  def existsEncoderFor(tpe: Type) = {
    OptionalTypecheck(c)(q"implicitly[${c.prefix}.Encoder[$tpe]]") match {
      case Some(enc) => true
      case None      => false
    }
  }
}

// TODO Maybe this should be a separate macro in the dynamic query case?
object MakeQuat extends MakeQuat {
  override def existsEncoderFor(tpe: quat.MakeQuat.u.Type): Boolean = true
}

trait MakeQuat extends QuatMakingBase {
  type Uni = scala.reflect.api.Universe
  lazy val u = scala.reflect.runtime.universe
  def of[T: u.TypeTag]: Quat = inferQuat(implicitly[u.TypeTag[T]].tpe)
}

trait QuatMakingBase {
  type Uni <: Universe
  val u: Uni
  import u.{ Block => _, Constant => _, Function => _, Ident => _, If => _, _ }

  def existsEncoderFor(tpe: Type): Boolean

  def inferQuat(tpe: Type): Quat = {

    // TODO Quat do we need other exclusions?
    def nonGenericMethods(tpe: Type) = {
      tpe.members
        .filter(m => m.isPublic
          && m.owner.name.toString != "Any"
          && m.owner.name.toString != "Object").map { param =>
          (param.name.toString, param.typeSignature.asSeenFrom(tpe, tpe.typeSymbol))
        }.toList
    }

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

    object ArbitraryBaseType {
      def unapply(tpe: Type): Option[(String, List[(String, Type)])] =
        if (tpe.widen.typeSymbol.isClass)
          Some((tpe.widen.typeSymbol.name.toString, nonGenericMethods(tpe.widen)))
        else
          None
    }

    object CaseClassBaseType {
      def unapply(tpe: Type): Option[(String, List[(String, Type)])] =
        if (tpe.widen.typeSymbol.isClass && tpe.widen.typeSymbol.asClass.isCaseClass)
          Some((tpe.widen.typeSymbol.name.toString, caseClassConstructorArgs(tpe.widen)))
        else
          None
    }

    object Signature {
      def unapply(tpe: Type) =
        Some(tpe.typeSymbol.typeSignature)
    }

    object Deoption {
      def unapply(tpe: Type) =
        if (isOptionType(tpe))
          Some(innerOptionParam(tpe, None))
        else
          Some(tpe)
    }

    def parseType(tpe: Type, boundedInterfaceType: Boolean = false): Quat =
      tpe match {
        // If there exists an encoder for the type assume it is a value
        case _ if existsEncoderFor(tpe) =>
          Quat.Value

        // If the type is optional, recurse
        case _ if (isOptionType(tpe)) =>
          val innerParam = innerOptionParam(tpe, None)
          parseType(innerParam)

        // If it is a query type, recurse into it
        case QueryType(tpe) =>
          parseType(tpe)

        // For cases where the type is actually a parameter with type bounds
        // and the upper bound is not final, assume that polymorphism is being used
        // and that the user wants to extend a class e.g.
        // trait Spirit { def grade: Int }
        // case class Gin(grade: Int) extends Spirit
        // def is80Prof[T <: Spirit] = quote { (spirit: Query[Spirit]) => spirit.filter(_.grade == 80) }
        // run(is80Proof(query[Gin]))
        // When processing is80Prof, we assume that Spirit is actually a base class to be extended
        case Signature(TypeBounds(lower, Deoption(upper))) if (upper != null && tpe.typeSymbol.isParameter && !upper.typeSymbol.isFinal) =>
          parseType(upper, true)

        case TypeBounds(lower, Deoption(upper)) if (upper != null && tpe.typeSymbol.isParameter && !upper.typeSymbol.isFinal) =>
          parseType(upper, true)

        case _ if (isNone(tpe)) =>
          Quat.Null
        // For other types of case classes
        case CaseClassBaseType(name, fields) =>
          Quat.Product(fields.map { case (fieldName, fieldType) => (fieldName, parseType(fieldType)) })

        // If we are already inside a bounded type, treat an arbitrary type as a interface list
        case ArbitraryBaseType(name, fields) if (boundedInterfaceType) =>
          Quat.Product(fields.map { case (fieldName, fieldType) => (fieldName, parseType(fieldType)) })

        // Otherwise it's a terminal value
        case _ =>
          Messages.trace(s"Could not infer SQL-type of ${tpe}, assuming it is a value.")
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
