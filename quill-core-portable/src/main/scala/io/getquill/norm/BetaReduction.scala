package io.getquill.norm

import io.getquill.ast._
import io.getquill.quat.Quat

import scala.collection.immutable.{ Map => IMap }

case class BetaReduction(replacements: Replacements)
  extends StatelessTransformer {

  override def apply(ast: Ast): Ast =
    ast match {

      case ast if replacements.contains(ast) =>
        val rep = BetaReduction(replacements - ast - replacements(ast))(replacements(ast))
        // TODO Detect if we're replacing something will null, synthesize a 'null' node
        //       that has the type of we were replacing it with
        (ast, rep) match {
          case (ast, OptionNone(Quat.Null)) =>
            OptionNone(ast.quat)
          case (_, rep) =>
            rep
        }
      //        rep

      case Property(Tuple(values), name) =>
        apply(values(name.drop(1).toInt - 1))

      case Property(CaseClass(tuples), name) =>
        apply(tuples.toMap.apply(name))

      case FunctionApply(Function(params, body), values) =>
        val conflicts = values.flatMap(CollectAst.byType[Ident]).map { i =>
          i -> Ident(s"tmp_${i.name}", i.quat)
        }.toMap[Ast, Ast]
        val newParams = params.map { p =>
          conflicts.getOrElse(p, p)
        }
        val bodyr = BetaReduction(Replacements(conflicts ++ params.zip(newParams))).apply(body)
        apply(BetaReduction(replacements ++ newParams.zip(values).toMap).apply(bodyr))

      case Function(params, body) =>
        val newParams = params.map { p =>
          replacements.get(p) match {
            case Some(i: Ident) => i
            case _              => p
          }
        }
        Function(newParams, BetaReduction(replacements ++ params.zip(newParams).toMap)(body))

      case Block(statements) =>
        apply {
          statements.reverse.tail.foldLeft((IMap[Ast, Ast](), statements.last)) {
            case ((map, stmt), line) =>
              BetaReduction(Replacements(map))(line) match {
                case Val(name, body) =>
                  val newMap = map + (name -> body)
                  val newStmt = BetaReduction(stmt, Replacements(newMap))
                  (newMap, newStmt)
                case _ =>
                  (map, stmt)
              }
          }._2
        }

      case Foreach(query, alias, body) =>
        Foreach(query, alias, BetaReduction(replacements - alias)(body))
      case Returning(action, alias, prop) =>
        val t = BetaReduction(replacements - alias)
        Returning(apply(action), alias, t(prop))

      case ReturningGenerated(action, alias, prop) =>
        val t = BetaReduction(replacements - alias)
        ReturningGenerated(apply(action), alias, t(prop))

      case other =>
        super.apply(other)
    }

  override def apply(o: OptionOperation): OptionOperation =
    o match {
      case other @ OptionTableFlatMap(a, b, c) =>
        OptionTableFlatMap(apply(a), b, BetaReduction(replacements - b)(c))
      case OptionTableMap(a, b, c) =>
        OptionTableMap(apply(a), b, BetaReduction(replacements - b)(c))
      case OptionTableExists(a, b, c) =>
        OptionTableExists(apply(a), b, BetaReduction(replacements - b)(c))
      case OptionTableForall(a, b, c) =>
        OptionTableForall(apply(a), b, BetaReduction(replacements - b)(c))
      case other @ OptionFlatMap(a, b, c) =>
        OptionFlatMap(apply(a), b, BetaReduction(replacements - b)(c))
      case OptionMap(a, b, c) =>
        OptionMap(apply(a), b, BetaReduction(replacements - b)(c))
      case OptionForall(a, b, c) =>
        OptionForall(apply(a), b, BetaReduction(replacements - b)(c))
      case OptionExists(a, b, c) =>
        OptionExists(apply(a), b, BetaReduction(replacements - b)(c))
      case other =>
        super.apply(other)
    }

  override def apply(e: Assignment): Assignment =
    e match {
      case Assignment(alias, prop, value) =>
        val t = BetaReduction(replacements - alias)
        Assignment(alias, t(prop), t(value))
    }

  override def apply(query: Query): Query =
    query match {
      case Filter(a, b, c) =>
        Filter(apply(a), b, BetaReduction(replacements - b)(c))
      case Map(a, b, c) =>
        Map(apply(a), b, BetaReduction(replacements - b)(c))
      case FlatMap(a, b, c) =>
        FlatMap(apply(a), b, BetaReduction(replacements - b)(c))
      case ConcatMap(a, b, c) =>
        ConcatMap(apply(a), b, BetaReduction(replacements - b)(c))
      case SortBy(a, b, c, d) =>
        SortBy(apply(a), b, BetaReduction(replacements - b)(c), d)
      case GroupBy(a, b, c) =>
        GroupBy(apply(a), b, BetaReduction(replacements - b)(c))
      case Join(t, a, b, iA, iB, on) =>
        Join(t, apply(a), apply(b), iA, iB, BetaReduction(replacements - iA - iB)(on))
      case FlatJoin(t, a, iA, on) =>
        FlatJoin(t, apply(a), iA, BetaReduction(replacements - iA)(on))
      case _: Take | _: Entity | _: Drop | _: Union | _: UnionAll | _: Aggregation | _: Distinct | _: Nested =>
        super.apply(query)
    }
}

object BetaReduction {

  private def checkQuats(body: Ast, replacements: Seq[(Ast, Ast)]) =
    replacements.foreach {
      case (orig, rep) =>
        //if (orig.quat != rep.quat)
        if (!orig.quat.canReduceTo(rep.quat))
          throw new IllegalArgumentException(s"Cannot beta reduce [$orig -> $rep] within [$body]. They have different types: ${orig.quat.shortString} and ${rep.quat.shortString}")
    }

  def apply(ast: Ast, t: (Ast, Ast)*): Ast = {
    // TODO Quat Remove this
    //    if (t.map(_._2).find(ast => ast.isInstanceOf[OptionNone]).isDefined) {
    //      println("Stop here")
    //    }
    checkQuats(ast, t)
    val output = apply(ast, Replacements(t.toMap))
    output
  }

  def apply(ast: Ast, replacements: Replacements): Ast = {
    checkQuats(ast, replacements.map.toSeq)
    BetaReduction(replacements).apply(ast) match {
      // Since it is possible for the AST to match but the match not be exactly the same (e.g.
      // if a AST property not in the product cases comes up (e.g. Ident's quat.rename etc...) make
      // sure to return the actual AST that was matched as opposed to the one passed in.
      case matchingAst @ `ast` => matchingAst
      case other               => apply(other, Replacements.empty)
    }
  }
}
