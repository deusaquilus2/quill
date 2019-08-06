package io.getquill.norm
import io.getquill.ast.Ast

/**
 * When doing beta reductions, certain properties or certain AST elements
 * need to be ignored so when looking up a Key or doing a Replace in the AST
 * map, we need to normalize the elements of the map.
 *
 * For example, the `Property` AST element has a field
 * called `renameable` which dicatates whether to use a `NamingStrategy`
 * during tokenization in `SqlIdiom` (and other idioms) or not. Since this property
 * only does things after Normalization, it should be completely transparent to
 * beta reduction. This is why we need to automatically set the `renameable` field to
 * a pre-defined value every time `Property` is looked up.
 *
 * For this reason, `BetaReduction` needs to a rule set that can potentially be a bit more
 * sophisticated then a simple map. This is why the `Replacements` class is created which
 * allows some customization of how the replacements in `BetaReduction` work.
 * In particular, the `ReplacementMapWithKeyTransform` class allows
 * the user to pass in a custom transformation to apply to keys before the
 * beta reduction matches them.
 */
object Replacements {
  def simpleMap(map: collection.Map[Ast, Ast]): Replacements =
    ReplacementMapWithKeyTransform(map, k => k)

  def pairs(t: (Ast, Ast)*): Replacements =
    simpleMap(t.toMap)

  def pairsWithKeyTransform(t: (Ast, Ast)*)(keyTransform: Ast => Ast) =
    ReplacementMapWithKeyTransform(t.toMap, keyTransform)
}

trait Replacements {
  def empty: Replacements
  def `new`(pairs: collection.Map[Ast, Ast]): Replacements = empty ++ pairs
  def `new`(pairs: Traversable[(Ast, Ast)]): Replacements = empty ++ pairs

  def apply(key: Ast): Ast
  def get(key: Ast): Option[Ast]
  def contains(key: Ast): Boolean
  def ++(newPairs: collection.Map[Ast, Ast]): Replacements
  def ++(newPairs: Traversable[(Ast, Ast)]): Replacements = ++(newPairs.toMap)
  def -(key: Ast): Replacements
}

case class ReplacementMapWithKeyTransform(map: collection.Map[Ast, Ast], keyTransform: (Ast) => Ast) extends Replacements {

  def transform(ast: Ast): Ast = keyTransform(ast)

  /** First transformed object to meet criteria **/
  def apply(key: Ast) =
    map.map { case (k, v) => (transform(k), v) }.filter(_._1 == transform(key)).head._2

  /** First transformed object to meet criteria or none of none meets **/
  def get(key: Ast) =
    map.map { case (k, v) => (transform(k), v) }.filter(_._1 == transform(key)).headOption.map(_._2)

  /** Does the map contain a normalized version of the view you want to see */
  def contains(key: Ast) =
    map.map { case (k, v) => transform(k) }.toList.contains(transform(key))

  def ++(otherMap: collection.Map[Ast, Ast]): ReplacementMapWithKeyTransform =
    ReplacementMapWithKeyTransform(map ++ otherMap, keyTransform)

  def -(key: Ast) = {
    val newMap = map.toList.filterNot { case (k, v) => transform(k) == transform(key) }.toMap
    ReplacementMapWithKeyTransform(newMap, keyTransform)
  }
  override def empty: Replacements =
    ReplacementMapWithKeyTransform(Map(), keyTransform)
}
