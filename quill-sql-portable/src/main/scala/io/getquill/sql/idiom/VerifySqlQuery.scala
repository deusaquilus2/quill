package io.getquill.context.sql.idiom

import io.getquill.ast._
import io.getquill.ast.Implicits._
import io.getquill.context.sql._
import io.getquill.quotation.{ FreeVariables }

case class Error(free: List[Ident], ast: Ast)
case class InvalidSqlQuery(errors: List[Error]) {
  override def toString =
    s"The monad composition can't be expressed using applicative joins. " +
      errors.map(error => s"Faulty expression: '${error.ast}'. Free variables: '${error.free}'.").mkString(", ")
}

object VerifySqlQuery {

  def apply(query: SqlQuery): Option[String] =
    verify(query).map(_.toString)

  private def verify(query: SqlQuery): Option[InvalidSqlQuery] =
    query match {
      case q: FlattenSqlQuery             => verify(q)
      case SetOperationSqlQuery(a, op, b) => verify(a).orElse(verify(b))
      case UnaryOperationSqlQuery(op, q)  => verify(q)
    }

  private def verifyFlatJoins(q: FlattenSqlQuery) = {

    def loop(l: List[FromContext], available: Set[String]): Set[String] =
      l.foldLeft(available) {
        case (av, TableContext(_, alias)) => Set(alias)
        case (av, InfixContext(_, alias)) => Set(alias)
        case (av, QueryContext(_, alias)) => Set(alias)
        case (av, JoinContext(_, a, b, on)) =>
          av ++ loop(a :: Nil, av) ++ loop(b :: Nil, av)
        case (av, FlatJoinContext(_, a, on)) =>
          val nav = av ++ loop(a :: Nil, av)
          val free = FreeVariables(on).map(_.name)
          val invalid = free -- nav
          require(
            invalid.isEmpty,
            s"Found an `ON` table reference of a table that is not available: $invalid. " +
              "The `ON` condition can only use tables defined through explicit joins."
          )
          nav
      }
    loop(q.from, Set())
  }

  private def verify(query: FlattenSqlQuery): Option[InvalidSqlQuery] = {

    verifyFlatJoins(query)

    val aliases = query.from.flatMap(this.aliases).map(IdentName(_)) :+ IdentName("*") :+ IdentName("?")

    def verifyAst(ast: Ast) = {
      val freeVariables =
        (FreeVariables(ast) -- aliases).toList
      val freeIdents =
        (CollectAst(ast) {
          case ast: Property            => None
          case Aggregation(_, _: Ident) => None
          case ast: Ident               => Some(ast)
        }).flatten
      (freeVariables ++ freeIdents.map(_.idName)) match {
        case Nil  => None
        case free => Some(Error(free.map(f => Ident(f.name, Quat.Value)), ast)) // Quat is not actually needed here here just for the sake of the Error Ident
      }
    }

    // Recursively expand children until values are fully flattened. Identities in all these should
    // be skipped during verification.
    def expandSelect(sv: SelectValue): List[SelectValue] =
      sv.ast match {
        case Tuple(values)     => values.map(v => SelectValue(v)).flatMap(expandSelect(_))
        case CaseClass(values) => values.map(v => SelectValue(v._2)).flatMap(expandSelect(_))
        case _                 => List(sv)
      }

    val freeVariableErrors: List[Error] =
      query.where.flatMap(verifyAst).toList ++
        query.orderBy.map(_.ast).flatMap(verifyAst) ++
        query.limit.flatMap(verifyAst) ++
        query.select
        .flatMap(expandSelect(_)) // Expand tuple select clauses so their top-level identities are skipped
        .map(_.ast)
        .filterNot(_.isInstanceOf[Ident]).flatMap(verifyAst) ++
        query.from.flatMap {
          case j: JoinContext     => verifyAst(j.on)
          case j: FlatJoinContext => verifyAst(j.on)
          case _                  => Nil
        }

    val nestedErrors =
      query.from.collect {
        case QueryContext(query, alias) => verify(query).map(_.errors)
      }.flatten.flatten

    (freeVariableErrors ++ nestedErrors) match {
      case Nil    => None
      case errors => Some(InvalidSqlQuery(errors))
    }
  }

  private def aliases(s: FromContext): List[String] =
    s match {
      case s: TableContext    => List(s.alias)
      case s: QueryContext    => List(s.alias)
      case s: InfixContext    => List(s.alias)
      case s: JoinContext     => aliases(s.a) ++ aliases(s.b)
      case s: FlatJoinContext => aliases(s.a)
    }
}
