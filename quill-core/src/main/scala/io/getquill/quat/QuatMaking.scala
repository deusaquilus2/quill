package io.getquill.quat

import io.getquill.dsl.QuotationDsl
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

  def existsImplicitEncoderFor(tpe: Type) = {
    OptionalTypecheck(c)(q"implicitly[${c.prefix}.Encoder[$tpe]]") match {
      case Some(enc) => true
      case None      => false
    }
  }

  import collection.mutable.HashMap;

  val cachedEncoderCheck: HashMap[Type, Boolean] = HashMap();

  def existsEncoderFor(tpe: Type): Boolean = {
    val cachedEntry = cachedEncoderCheck.get(tpe)
    cachedEntry match {
      case None =>
        val lookup = existsImplicitEncoderFor(tpe)
        cachedEncoderCheck.put(tpe, lookup)
        lookup

      case Some(value) =>
        value
    }
  }
}

// TODO Write a macro to use in dynamic-query cases that will check quats against existing implicits
//      in the context (i.e. to see what encoders there are for better quat generation)

trait MakeQuatRuntime extends QuatMakingBase {
  type Uni = scala.reflect.api.Universe
  lazy val u = scala.reflect.runtime.universe
  def of[T](implicit tt: u.TypeTag[T]): Quat = inferQuat(tt.tpe)
  override def existsEncoderFor(tpe: u.Type): Boolean = false
}

object MakeQuat extends MakeQuatRuntime

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
          (param.name.toString, param.typeSignature)
        }.toList
    }

    def caseClassConstructorArgs(tpe: Type) = {
      val constructor =
        tpe.members.collect {
          case m: MethodSymbol if m.isPrimaryConstructor => m
        }.head

      // TODO Quat Only one constructor param list supported so far? Have an error for that?
      constructor.paramLists(0).map { param =>
        (param.name.toString, param.typeSignature)
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

    object Param {
      def unapply(tpe: Type) =
        if (tpe.typeSymbol.isParameter)
          Some(tpe)
        else
          None
    }

    object RealTypeBounds {
      def unapply(tpe: Type) =
        tpe match {
          case TypeBounds(lower, upper) if (upper != null && !(upper =:= typeOf[Any])) =>
            Some((lower, upper))
          case _ =>
            None
        }
    }

    object DefiniteValue {
      def unapply(tpe: Type): Option[Type] = {
        // UDTs (currently only used by cassandra) are reated as tables even though there is an encoder for them.
        if (tpe <:< typeOf[io.getquill.Udt])
          None
        else if (isType[AnyVal](tpe))
          Some(tpe)
        else
          None
      }
    }

    def parseTopLevelType(tpe: Type): Quat =
      tpe match {
        case DefiniteValue(tpe) =>
          Quat.Value

        // If it is a query type, recurse into it
        case QueryType(tpe) =>
          parseType(tpe)

        // TODO Quat Is this situation needed? What are the cases where top-level type is Query[T]?
        // case QueryType(Param(tpe)) =>
        //   parseType(tpe)

        // For cases where the type is actually a parameter with type bounds
        // and the upper bound is not final, assume that polymorphism is being used
        // and that the user wants to extend a class e.g.
        // trait Spirit { def grade: Int }
        // case class Gin(grade: Int) extends Spirit
        // def is80Prof[T <: Spirit] = quote { (spirit: Query[Spirit]) => spirit.filter(_.grade == 80) }
        // run(is80Proof(query[Gin]))
        // When processing is80Prof, we assume that Spirit is actually a base class to be extended
        case Param(Signature(RealTypeBounds(lower, Deoption(upper)))) if (!upper.typeSymbol.isFinal && !existsEncoderFor(tpe)) =>
          parseType(upper, true)

        case Param(RealTypeBounds(lower, Deoption(upper))) if (!upper.typeSymbol.isFinal && !existsEncoderFor(tpe)) =>
          parseType(upper, true)

        case Param(tpe) =>
          Quat.Generic

        case other =>
          parseType(other)
      }

    /**
     * Quat parsing has a top-level type parsing function and then secondary function which is recursed. This is because
     * things like type boundaries (e.g.  type-bounds types (e.g. Query[T &lt;: BaseType]) should only be checked once
     * at the top level.
     */
    def parseType(tpe: Type, boundedInterfaceType: Boolean = false): Quat =
      tpe match {
        case DefiniteValue(tpe) =>
          Quat.Value

        // This will happens for val-parsing situations e.g. where you have val (a,b) = (Query[A],Query[B]) inside a quoted block.
        // In this situations, the CaseClassBaseType should activate first and recurse which will then hit this case clause.
        case QueryType(tpe) =>
          parseType(tpe)

        // If the type is optional, recurse
        case _ if (isOptionType(tpe)) =>
          val innerParam = innerOptionParam(tpe, None)
          parseType(innerParam)

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

    parseTopLevelType(tpe)
  }

  object QuotedType {
    def unapply(tpe: Type) =
      paramOf(tpe, typeOf[QuotationDsl#Quoted[Any]])
  }

  object QueryType {
    def unapply(tpe: Type) =
      paramOf(tpe, typeOf[io.getquill.Query[Any]])
  }

  object TypeSigParam {
    def unapply(tpe: Type): Option[Type] =
      tpe.typeSymbol.typeSignature.typeParams match {
        case head :: tail => Some(head.typeSignature)
        case Nil          => None
      }
  }

  // TODO Quat remove comments
  def paramOf(tpe: Type, of: Type, maxDepth: Int = 10): Option[Type] = {
    //println(s"### Attempting to check paramOf ${tpe} assuming it is a ${of}")
    tpe match {
      case _ if (maxDepth == 0) =>
        throw new IllegalArgumentException(s"Max Depth reached with type: ${tpe}")
      case _ if (!(tpe <:< of)) =>
        //println(s"### ${tpe} is not a ${of}")
        None
      case _ if (tpe =:= typeOf[Nothing] || tpe =:= typeOf[Any]) =>
        //println(s"### ${tpe} is Nothing or Any")
        None
      case TypeRef(_, cls, List(arg)) =>
        //println(s"### ${tpe} is a TypeRef whose arg is ${arg}")
        Some(arg)
      case TypeSigParam(param) =>
        //println(s"### ${tpe} is a type signature whose type is ${param}")
        Some(param)
      case _ =>
        val base = tpe.baseType(of.typeSymbol)
        //println(s"### Going to base type for ${tpe} for expected base type ${of}")
        paramOf(base, of, maxDepth - 1)
    }
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

  private[getquill] def isType[T](tpe: Type)(implicit tt: TypeTag[T]) =
    tpe <:< tt.tpe
}
