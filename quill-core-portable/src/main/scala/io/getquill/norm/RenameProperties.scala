package io.getquill.norm

import io.getquill.ast._
import io.getquill.quat.Quat
import io.getquill.util.Messages.title

/**
 * Rename properties now relies on the Quats themselves to propagate field renames. The previous
 * itreations of this phase relied on schema propagation via stateful transforms holding
 * field-renames which were then compared to Property AST elements. This was a painstakingly complex and
 * highly error-prone especially when embedded objects were used requiring computation of sub-schemas
 * in a process called 'schema protraction'.
 * The new variation of this phase relies on the Quats directly since the Quats of every Identity, Lift, etc...
 * now know what the field-names contained therein as well as the sub-Quats of any embedded property.
 * This is fairly simple process:
 *
 * <ul>
 * <li> Learning what Quats have which renames is simple since this can be propagated from the Quats of the Entity objects,
 * to the rest of the AST.
 * <li> This has the simple requirement that renames must be propagated fully before they are actually committed
 * so that the knowledge of what needs to be renamed into what can be distributed easily throughout the AST.
 * <li> Once these future-renames are staged to Quats throught the AST, a simple stateless reduction will then apply
 * the renames to the Property AST elements around the Ident's (and potentially Lifts etc...) with the renamed Quats.
 * </ul>
 *
 * The entire process above can be done with a series of stateless transformations with straighforward operations
 * since the majority of the logic actually lives within the Quats themselves.
 */
object NewRenameProperties {
  private def demarcate(heading: String) =
    ((ast: Ast) => title(heading)(ast))

  def apply(ast: Ast) = {
    (identity[Ast] _)
      .andThen(SeedRenames.apply(_: Ast)) // Stage field renames into the Quats of entities
      .andThen(demarcate("SeedRenames"))
      .andThen(RepropagateQuats.apply(_: Ast))
      .andThen(demarcate("RepropagateQuats")) // Propagate the renames from Entity-Quats to the rest of the Quats in the AST
      .andThen(ApplyRenamesToProps.apply(_: Ast))
      .andThen(demarcate("ApplyRenamesToProps")) // Go through the Quats and 'commit' the renames
      .andThen(CompleteRenames.apply(_: Ast))
      .andThen(demarcate("CompleteRenames"))(ast) // Quats can be invalid in between this phase and the previous one
  }
}

object CompleteRenames extends StatelessTransformer {
  // TODO Quat apply this logic to entities as well
  override def applyIdent(e: Ident): Ident = e match {
    case e: Ident =>
      e.copy(quat = e.quat.applyRenames)
  }

  override def apply(e: Ast): Ast = e match {
    case e: Ident =>
      e.copy(quat = e.quat.applyRenames)

    case other =>
      super.apply(other)
  }
}

/** Take renames propogated to the quats and apply them to properties */
object ApplyRenamesToProps extends StatelessTransformer {
  override def apply(e: Ast): Ast = e match {

    case p @ Property.Opinionated(ast, name, renameable, visibility) =>
      val newAst = apply(ast)
      // Check the quat if it is renaming this property if so rename it. Otherwise property is the same
      newAst.quat.renames.find(_._1 == name) match {
        case Some((_, newName)) =>
          Property.Opinionated(newAst, newName, renameable, visibility)
        case None => p
      }

    case other => super.apply(other)
  }
}

object SeedRenames extends StatelessTransformer {
  override def apply(e: Query): Query =
    e match {
      case e: Entity => e.syncToQuat
      case _         => super.apply(e)
    }
}

object RepropagateQuats extends StatelessTransformer {
  import TypeBehavior.{ ReplaceWithReduction => RWR }

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
      case Filter(a, b, c) => applyBody(a, b, c)(Filter)
      case Map(a, b, c) =>
        applyBody(a, b, c)(Map)
      case FlatMap(a, b, c)   => applyBody(a, b, c)(FlatMap)
      case ConcatMap(a, b, c) => applyBody(a, b, c)(ConcatMap)
      case GroupBy(a, b, c)   => applyBody(a, b, c)(GroupBy)
      case SortBy(a, b, c, d) => applyBody(a, b, c)(SortBy(_, _, _, d))
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
      case Assignment(alias, property, value) =>
        val aliasR = alias.withQuat(quat)
        val propertyR = BetaReduction(property, RWR, alias -> aliasR)
        val valueR = BetaReduction(value, RWR, alias -> aliasR)
        Assignment(aliasR, propertyR, valueR)
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

      case Returning(action: Action, alias, body) =>
        val actionR = apply(action)
        val aliasR = alias.withQuat(actionR.quat)
        val bodyR = BetaReduction(body, RWR, alias -> aliasR)
        Returning(actionR, aliasR, bodyR)

      case ReturningGenerated(action: Action, alias, body) =>
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
                case prop @ PropertyMatroshka(ident, _) =>
                  BetaReduction(prop, RWR, ident -> ident.withQuat(oca.quat)).asInstanceOf[Property]
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
                val aliasR = assignment.alias.copy(quat = oca.quat)
                val propertyR = BetaReduction(assignment.property, RWR, assignment.alias -> aliasR)
                val valueR = BetaReduction(assignment.value, RWR, assignment.alias -> aliasR)
                Assignment(aliasR, propertyR, valueR)
              }
            OnConflict.Update(assignmentsR)
          case _ => act
        }
        OnConflict(actionR, targetR, actR)

      case other => super.apply(other)
    }
}

// Represents a nested property path to an identity i.e. Property(Property(... Ident(), ...))
object PropertyMatroshka {

  def traverse(initial: Property): Option[(Ident, List[String])] =
    initial match {
      // If it's a nested-property walk inside and append the name to the result (if something is returned)
      case Property(inner: Property, name) =>
        traverse(inner).map { case (id, list) => (id, list :+ name) }
      // If it's a property with ident in the core, return that
      case Property(id: Ident, name) =>
        Some((id, List(name)))
      // Otherwise an ident property is not inside so don't return anything
      case _ =>
        None
    }

  def unapply(ast: Ast): Option[(Ident, List[String])] =
    ast match {
      case p: Property => traverse(p)
      case _           => None
    }

}
