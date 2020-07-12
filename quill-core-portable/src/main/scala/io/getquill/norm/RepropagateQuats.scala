package io.getquill.norm

import io.getquill.ast.{ Action, Assignment, Ast, ConcatMap, Filter, FlatJoin, FlatMap, GroupBy, Ident, Insert, Join, Map, OnConflict, Property, Query, Returning, ReturningGenerated, SortBy, StatelessTransformer, Update }
import io.getquill.quat.Quat

sealed trait RepropagationBehavior
object RepropagationBehavior {
  case object AllIdents extends RepropagationBehavior
  case object OnlyGeneric extends RepropagationBehavior
}

object RepropagateQuats {
  def apply(ast: Ast) =
    new RepropagateQuats(RepropagationBehavior.AllIdents)(ast)

  def Generic(ast: Ast) =
    new RepropagateQuats(RepropagationBehavior.OnlyGeneric)(ast)
}

case class RepropagateQuats(behavior: RepropagationBehavior) extends StatelessTransformer {
  import TypeBehavior.{ ReplaceWithReduction => RWR }

  object Reprop {
    def apply(id: Ident): Boolean =
      unapply(id).isDefined

    def unapply(id: Ident) =
      behavior match {
        case RepropagationBehavior.AllIdents =>
          Some(id)
        case RepropagationBehavior.OnlyGeneric =>
          id.quat match {
            case Quat.Generic =>
              Some(id)
            case _ =>
              None
          }
      }
  }

  implicit class IdentExt(id: Ident) {
    def withQuat(from: Quat) =
      id.copy(quat = from)
  }

  def applyBody(a: Ast, b: Ident, c: Ast)(f: (Ast, Ident, Ast) => Query) = {
    val ar = apply(a)
    val br = b.withQuat(ar.quat)
    val cr = BetaReduction(c, RWR, b -> br)
    f(ar, br, apply(cr))
  }

  override def apply(e: Query): Query =
    // TODO Quat Do I need to do something for infixes?
    e match {
      case Filter(a, Reprop(b), c) => applyBody(a, b, c)(Filter)
      case Map(a, Reprop(b), c) =>
        applyBody(a, b, c)(Map)
      case FlatMap(a, Reprop(b), c)   => applyBody(a, b, c)(FlatMap)
      case ConcatMap(a, Reprop(b), c) => applyBody(a, b, c)(ConcatMap)
      case GroupBy(a, Reprop(b), c)   => applyBody(a, b, c)(GroupBy)
      case SortBy(a, Reprop(b), c, d) => applyBody(a, b, c)(SortBy(_, _, _, d))
      case Join(t, a, b, iA, iB, on) =>
        val ar = apply(a)
        val br = apply(b)
        val iAr = iA.withQuat(ar.quat)
        val iBr = iB.withQuat(br.quat)
        val onr = BetaReduction(on, RWR, iA -> iAr, iB -> iBr)
        Join(t, ar, br, iAr, iBr, apply(onr))
      case FlatJoin(t, a, iA, on) =>
        val ar = apply(a)
        val iAr = iA.withQuat(ar.quat)
        val onr = BetaReduction(on, RWR, iA -> iAr)
        FlatJoin(t, a, iAr, apply(onr))
      case other => super.apply(other)
    }

  def reassign(assignments: List[Assignment], quat: Quat) =
    assignments.map {
      case Assignment(Reprop(alias), property, value) =>
        val aliasR = alias.withQuat(quat)
        val propertyR = BetaReduction(property, RWR, alias -> aliasR)
        val valueR = BetaReduction(value, RWR, alias -> aliasR)
        Assignment(aliasR, propertyR, valueR)

      // If the alias is not supposed to be repropagated
      case assignment =>
        assignment
    }

  override def apply(a: Action): Action =
    a match {
      case Insert(q: Query, assignments) =>
        val qr = apply(q)
        val assignmentsR = reassign(assignments, qr.quat)
        Insert(qr, assignmentsR)

      case Update(q: Query, assignments) =>
        val qr = apply(q)
        val assignmentsR = reassign(assignments, qr.quat)
        Update(qr, assignmentsR)

      case Returning(action: Action, Reprop(alias), body) =>
        val actionR = apply(action)
        val aliasR = alias.withQuat(actionR.quat)
        val bodyR = BetaReduction(body, RWR, alias -> aliasR)
        Returning(actionR, aliasR, bodyR)

      case ReturningGenerated(action: Action, Reprop(alias), body) =>
        val actionR = apply(action)
        val aliasR = alias.withQuat(actionR.quat)
        val bodyR = BetaReduction(body, RWR, alias -> aliasR)
        ReturningGenerated(actionR, aliasR, bodyR)

      case oc @ OnConflict(oca: Action, target, act) =>
        val actionR = apply(oca)
        val targetR =
          target match {
            case OnConflict.Properties(props) =>
              val propsR = props.map {
                // Recreate the assignment with new idents but only if we need to repropagate
                case prop @ PropertyMatroshka(ident, _) =>
                  ident match {
                    case Reprop(_) =>
                      BetaReduction(prop, RWR, ident -> ident.withQuat(oca.quat)).asInstanceOf[Property]
                    case _ =>
                      prop
                  }
                case other =>
                  throw new IllegalArgumentException(s"Malformed onConflict element ${oc}. Could not parse property ${other}")
              }
              OnConflict.Properties(propsR)

            case v @ OnConflict.NoTarget => v
          }
        val actR = act match {
          case OnConflict.Update(assignments) =>
            val assignmentsR =
              assignments.map { assignment =>
                assignment.alias match {
                  case Reprop(_) =>
                    val aliasR = assignment.alias.copy(quat = oca.quat)
                    val propertyR = BetaReduction(assignment.property, RWR, assignment.alias -> aliasR)
                    val valueR = BetaReduction(assignment.value, RWR, assignment.alias -> aliasR)
                    Assignment(aliasR, propertyR, valueR)
                  case _ =>
                    assignment
                }
              }
            OnConflict.Update(assignmentsR)
          case _ => act
        }
        OnConflict(actionR, targetR, actR)

      case other => super.apply(other)
    }
}
