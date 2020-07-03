package io.getquill.context.sql.norm

import io.getquill.ast._
import io.getquill.ast.Implicits._
import io.getquill.norm.BetaReduction
import io.getquill.norm.TypeBehavior.{ ReplaceWithReduction => RWR }
import io.getquill.norm.Normalize
import io.getquill.quat.Quat

object ExpandJoin {

  def apply(q: Ast) = expand(q, None)

  def expand(q: Ast, id: Option[Ident]) =
    Transform(q) {
      case q @ Join(_, _, _, Ident(a, _), Ident(b, _), _) => // Ident a and Ident b should have the same Quat, could add an assertion for that
        val (qr, tuple) = expandedTuple(q)
        val innermostOpt =
          CollectAst(qr) {
            case fm @ FlatMap(_, _, MoreTables) => fm
          }.headOption

        val ret =
          innermostOpt match {
            case Some(innermost) =>
              val newInnermost =
                innermost match {
                  case FlatMap(fj: FlatJoin, alias, MoreTables) =>
                    val fjr = BetaReduction(fj, RWR, MoreCond -> (Constant(1) +==+ Constant(1))) // TODO reduce this out i.e. something && 1==1 should be just something
                    Map(fjr, alias, tuple)
                }
              val output = BetaReduction(qr, RWR, innermost -> newInnermost)
              output
            // TODO Quat Search for placeholders and throw exception if they're found

            case None => qr
          }

        ret
    }

  val MoreTables = Ident("<PH>", Quat.Error("MoreTables Place Holder needs to be removed from AST once join expansion is complete"))
  val MoreCond = Ident("<PH>", Quat.Error("MoreConditionals Place Holder needs to be removed from AST once join expansion is complete"))

  private def expandedTuple(q: Join): (FlatMap, Tuple) =
    q match {

      case Join(t, a: Join, b: Join, tA, tB, o) =>
        val (ar, at) = expandedTuple(a)
        val (br, bt) = expandedTuple(b)
        val or = BetaReduction(o, RWR, tA -> at, tB -> bt)
        val arbrFlat = BetaReduction(ar, RWR, MoreTables -> br)
        val arbr = BetaReduction(arbrFlat, RWR, MoreCond -> or).asInstanceOf[FlatMap] // Reduction of a flatMap must be a flatMap
        (arbr, Tuple(List(at, bt)))

      case Join(t, a: Join, b, tA, tB, o) =>
        val (ar, at) = expandedTuple(a)
        val or = BetaReduction(o, RWR, tA -> at)
        val br =
          FlatMap(
            FlatJoin(t, b, tB, or +&&+ MoreCond),
            tB, MoreTables
          )
        val arbr = BetaReduction(ar, RWR, MoreTables -> br).asInstanceOf[FlatMap]
        (arbr, Tuple(List(at, tB)))

      case Join(t, a, b: Join, tA, tB, o) =>
        val (br, bt) = expandedTuple(b)
        val or = BetaReduction(o, RWR, tB -> bt)
        val arbr =
          FlatMap(
            FlatJoin(t, a, tA, or),
            tA,
            BetaReduction(br, RWR, MoreCond -> or)
          )

        (arbr, Tuple(List(tA, bt)))

      case q @ Join(t, a, b, tA, tB, on) =>
        val ab =
          FlatMap(
            a, tA,
            FlatMap(FlatJoin(t, b, tB, on), tB, MoreTables)
          )

        (ab, Tuple(List(tA, tB)))
    }

  private def nestedExpand(q: Ast, id: Ident) =
    Normalize(expand(q, Some(id))) match {
      case Map(q, _, _) => q
      case q            => q
    }
}