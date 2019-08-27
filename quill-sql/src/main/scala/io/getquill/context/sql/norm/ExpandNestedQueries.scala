package io.getquill.context.sql.norm

import io.getquill.{ NamingStrategy, PseudoAst }
import io.getquill.ast.Ast
import io.getquill.ast.Ident
import io.getquill.ast._
import io.getquill.ast.StatefulTransformer
import io.getquill.context.sql.FlattenSqlQuery
import io.getquill.context.sql.FromContext
import io.getquill.context.sql.InfixContext
import io.getquill.context.sql.JoinContext
import io.getquill.context.sql.QueryContext
import io.getquill.context.sql.SelectValue
import io.getquill.context.sql.SetOperationSqlQuery
import io.getquill.context.sql.SqlQuery
import io.getquill.context.sql.TableContext
import io.getquill.context.sql.UnaryOperationSqlQuery
import io.getquill.context.sql.FlatJoinContext

import scala.collection.mutable.LinkedHashSet
import io.getquill.util.Interpolator
import io.getquill.util.Messages.TraceType.NestedQueryExpansion

class ExpandNestedQueries(strategy: NamingStrategy) {
  val interp = new Interpolator(NestedQueryExpansion, 3)
  import interp._

  def apply(q: SqlQuery, references: List[Property]): SqlQuery =
    apply(q, LinkedHashSet.empty ++ references)

  // Using LinkedHashSet despite the fact that it is mutable because it has better characteristics then ListSet.
  // Also this collection is strictly internal to ExpandNestedQueries and exposed anywhere else.
  private def apply(q: SqlQuery, references: LinkedHashSet[Property]): SqlQuery =
    q match {
      case q: FlattenSqlQuery =>
        val expand = expandNested(q.copy(select = expandSelect(q.select, references)))
        trace"Expanded Nested Query $q into $expand" andLog ()
        expand
      case SetOperationSqlQuery(a, op, b) =>
        SetOperationSqlQuery(apply(a, references), op, apply(b, references))
      case UnaryOperationSqlQuery(op, q) =>
        UnaryOperationSqlQuery(op, apply(q, references))
    }

  private def expandNested(q: FlattenSqlQuery): SqlQuery =
    q match {
      case FlattenSqlQuery(from, where, groupBy, orderBy, limit, offset, select, distinct) =>
        val asts = Nil ++ select.map(_.ast) ++ where ++ groupBy ++ orderBy.map(_.ast) ++ limit ++ offset
        val from = q.from.map(expandContext(_, asts))
        q.copy(from = from)
    }

  private def expandContext(s: FromContext, asts: List[Ast]): FromContext =
    s match {
      case QueryContext(q, alias) =>
        QueryContext(apply(q, references(alias, asts)), alias)
      case JoinContext(t, a, b, on) =>
        JoinContext(t, expandContext(a, asts :+ on), expandContext(b, asts :+ on), on)
      case FlatJoinContext(t, a, on) =>
        FlatJoinContext(t, expandContext(a, asts :+ on), on)
      case _: TableContext | _: InfixContext => s
    }

  /**
   * In order to be able to reconstruct the original ordering of elements inside of a select clause,
   * we need to keep track of their order, not only within the top-level select but also it's order
   * within any possible tuples/case-classes that in which it is embedded.
   * For example, in the query:
   * <pre><code>
   *   query[Person].map(p => (p.id, (p.name, p.age))
   * </code></pre>
   * Since the `p.name` and `p.age` elements are selected inside of a sub-tuple, their "order" is
   * `List(2,1)` and `List(2,2)` respectively as opposed to `p.id` whose "order" is just `List(1)`.
   */
  case class OrderedSelect(order: List[Int], selectValue: SelectValue) extends PseudoAst {
    override def toString: String = s"[${order.mkString(",")}]${selectValue}"
  }
  object OrderedSelect {
    def apply(order: Int, selectValue: SelectValue) =
      new OrderedSelect(List(order), selectValue)
  }

  case class DoubleOrderedSelect(order: List[Int], secondaryOrder: Int, selectValue: SelectValue)
  object DoubleOrderedSelect {
    def apply(os: OrderedSelect, secondaryOrder: Int): DoubleOrderedSelect =
      new DoubleOrderedSelect(os.order, secondaryOrder, os.selectValue)
  }

  private def expandSelect(selectValues: List[SelectValue], references: LinkedHashSet[Property]): List[SelectValue] = {
    trace"Expanding Select values: $selectValues into references: $references" andLog ()

    val select =
      selectValues.zipWithIndex.map {
        case (value, index) => OrderedSelect(index, value)
      }

    object TupleIndex {
      def unapply(s: String): Option[Int] =
        if (s.matches("_[0-9]*"))
          Some(s.drop(1).toInt - 1)
        else
          None
    }

    object MultiTupleIndex {
      def unapply(s: String): Boolean =
        if (s.matches("(_[0-9]+)+"))
          true
        else
          false
    }

    def expandColumn(name: String, renameable: Renameable): String =
      renameable.fixedOr(name)(strategy.column(name))

    def expandReference(ref: Property): OrderedSelect = {
      trace"Expanding: $ref from $select" andLog ()

      def expressIfTupleIndex(str: String) =
        str match {
          case MultiTupleIndex() => Some(str)
          case _                 => None
        }

      def concat(alias: Option[String], idx: Int) =
        Some(s"${alias.getOrElse("")}_${idx + 1}")

      val orderedSelect = ref match {
        case pp @ Property(ast: Property, TupleIndex(idx)) =>
          trace"Reference is a sub-property of a tuple index: $idx. Walking inside." andContinue
            expandReference(ast) match {
              case OrderedSelect(o, SelectValue(Tuple(elems), alias, c)) =>
                trace"Expressing Element $idx of $elems " andReturn
                OrderedSelect(o :+ idx, SelectValue(elems(idx), concat(alias, idx), c))
              case OrderedSelect(o, SelectValue(ast, alias, c)) =>
                trace"Appending $idx to $alias " andReturn
                OrderedSelect(o, SelectValue(ast, concat(alias, idx), c))
            }
        case pp @ Property.Opinionated(ast: Property, name, renameable) =>
          trace"Reference is a sub-property. Walking inside." andContinue
            expandReference(ast) match {
              case OrderedSelect(o, SelectValue(ast, nested, c)) =>
                // Alias is the name of the column after the naming strategy
                // The clauses in `SqlIdiom` that use `Tokenizer[SelectValue]` select the
                // alias field when it's value is Some(T).
                // Technically the aliases of a column should not be using naming strategies
                // but this is an issue to fix at a later date.

                // In the current implementation, aliases we add nested tuple names to queries e.g.
                // SELECT foo from
                // SELECT x, y FROM (SELECT foo, bar, red, orange FROM baz JOIN colors)
                // Typically becomes SELECT foo _1foo, _1bar, _2red, _2orange when
                // this kind of query is the result of an applicative join that looks like this:
                // query[baz].join(query[colors]).nested
                // this may need to change based on how distinct appends table names instead of just tuple indexes
                // into the property path.

                OrderedSelect(o, SelectValue(
                  Property.Opinionated(ast, name, renameable),
                  Some(s"${nested.flatMap(expressIfTupleIndex(_)).getOrElse("")}${expandColumn(name, renameable)}"), c
                ))
            }
        case pp @ Property(_, TupleIndex(idx)) =>
          trace"Reference is a tuple index: $idx from $select." andContinue
            select(idx) match {
              case OrderedSelect(o, SelectValue(ast, alias, c)) =>
                OrderedSelect(o, SelectValue(ast, concat(alias, idx), c))
            }
        case pp @ Property.Opinionated(_, name, renameable) =>
          select match {
            case List(OrderedSelect(o, SelectValue(cc: CaseClass, alias, c))) =>
              // Currently case class element name is not being appended. Need to change that in order to ensure
              // path name uniqueness in future.
              val ((_, ast), index) = cc.values.zipWithIndex.find(_._1._1 == name) match {
                case Some(v) => v
                case None    => throw new IllegalArgumentException(s"Cannot find element $name in $cc")
              }
              trace"Reference is a case class member: " andReturn
                OrderedSelect(o :+ index, SelectValue(ast, Some(expandColumn(name, renameable)), c))
            case List(OrderedSelect(o, SelectValue(i: Ident, _, c))) =>
              trace"Reference is an identifier: " andReturn
                OrderedSelect(o, SelectValue(Property.Opinionated(i, name, renameable), None, c))
            case other =>
              trace"Reference is unidentified: " andReturn
                OrderedSelect(Integer.MAX_VALUE, SelectValue(Ident(name), Some(expandColumn(name, renameable)), false))
          }
      }

      trace"Expanded $ref into $orderedSelect"
      orderedSelect
    }

    /**
     * The challenge with appeneding infixes (that have not been used but are still needed)
     * back into the query, is that they could be inside of tuples/case-classes that have already
     * been selected, or inside of sibling elements which have been selected.
     * Take for instance a query that looks like this:
     * <pre><code>
     *   query[Person].map(p => (p.name, (p.id, infix"foo(${p.other})".as[Int]))).map(p => (p._1, p._2._1))
     * </code></pre>
     * In this situation, `p.id` which is the sibling of the non-selected infix has been selected
     * via `p._2._1` (whose select-order is List(1,0) to represent 1st element in 2nd tuple.
     * We need to add it's sibling infix.
     *
     * Or take the following situation:
     * <pre><code>
     *   query[Person].map(p => (p.name, (p.id, infix"foo(${p.other})".as[Int]))).map(p => (p._1, p._2))
     * </code></pre>
     * In this case, we have selected the entire 2nd element including the infix. We need to know that
     * `P._2._2` does not need to be selected since `p._2` was.
     *
     * In order to do these things, we use the `order` property from `OrderedSelect` in order to see
     * which sub-sub-...-element has been selected. If `p._2` (that has order `List(1)`)
     * has been selected, we know that any infixes inside of it e.g. `p._2._1` (ordering `List(1,0)`)
     * does not need to be.
     */
    def findUnexpressedInfixes(refs: List[DoubleOrderedSelect]) = {

      def pathExists(path: List[Int]) =
        refs.map(_.order).contains(path)

      def containsInfix(ast: Ast) =
        CollectAst.byType[Infix](ast).length > 0

      // build paths to every infix and see these paths were not selected already
      def findMissingInfixes(ast: Ast, parentOrder: List[Int]): List[(Ast, List[Int])] = {
        trace"Searching for infix: $ast in the sub-path $parentOrder" andLog ()
        if (pathExists(parentOrder))
          trace"No infixes found" andContinue
            List()
        else
          ast match {
            case Tuple(values) =>
              values.zipWithIndex
                .filter(v => containsInfix(v._1))
                .flatMap {
                  case (ast, index) =>
                    findMissingInfixes(ast, parentOrder :+ index)
                }
            case CaseClass(values) =>
              values.zipWithIndex
                .filter(v => containsInfix(v._1._2))
                .flatMap {
                  case ((_, ast), index) =>
                    findMissingInfixes(ast, parentOrder :+ index)
                }
            case other if (containsInfix(other)) =>
              trace"Found unexpressed infix inside $other in $parentOrder" andLog ()
              List((other, parentOrder))
            case _ =>
              List()
          }
      }

      select
        .flatMap {
          case OrderedSelect(o, sv) => findMissingInfixes(sv.ast, o)
        }.map {
          case (ast, order) => DoubleOrderedSelect(order, 0, SelectValue(ast))
        }
    }

    references.toList match {
      case Nil => select.map(_.selectValue)
      case refs => {
        // elements first need to be sorted by their order in the select clause. Since some may map to multiple
        // properties when expanded, we want to maintain this order of properties as a secondary value.
        val mappedRefs =
          refs.map(expandReference).zipWithIndex.map {
            case (ref, secondIndex) => DoubleOrderedSelect(ref, secondIndex)
          }
        trace"Mapped Refs: $mappedRefs" andLog ()

        // are there any selects that have infix values which we have not already selected? We need to include
        // them because they could be doing essential things e.g. RANK ... ORDER BY
        val remainingSelectsWithInfixes =
          trace"Searching Selects with Infix:" andReturn
            findUnexpressedInfixes(mappedRefs)

        implicit val ordering: scala.math.Ordering[List[Int]] = new scala.math.Ordering[List[Int]] {
          override def compare(x: List[Int], y: List[Int]): Int =
            (x, y) match {
              case (head1 :: tail1, head2 :: tail2) =>
                val diff = head1 - head2
                if (diff != 0) diff
                else compare(tail1, tail2)
              case (Nil, Nil)   => 0 // List(1,2,3) == List(1,2,3)
              case (head1, Nil) => -1 // List(1,2,3) < List(1,2)
              case (Nil, head2) => 1 // List(1,2) > List(1,2,3)
            }
        }

        val sortedRefs =
          (mappedRefs ++ remainingSelectsWithInfixes).sortBy(ref => (ref.order, ref.secondaryOrder))

        sortedRefs.map(_.selectValue)
      }
    }
  }

  private def references(alias: String, asts: List[Ast]) =
    LinkedHashSet.empty ++ (References(State(Ident(alias), Nil))(asts)(_.apply)._2.state.references)
}

case class State(ident: Ident, references: List[Property])

case class References(val state: State)
  extends StatefulTransformer[State] {

  import state._

  override def apply(a: Ast) =
    a match {
      case `reference`(p) => (p, References(State(ident, references :+ p)))
      case other          => super.apply(a)
    }

  object reference {
    def unapply(p: Property): Option[Property] =
      p match {
        case Property(`ident`, name)      => Some(p)
        case Property(reference(_), name) => Some(p)
        case other                        => None
      }
  }
}
