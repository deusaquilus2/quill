package io.getquill.norm

import io.getquill.ast._
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
