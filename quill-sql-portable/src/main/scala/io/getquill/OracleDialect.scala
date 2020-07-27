package io.getquill

import io.getquill.ast._
import io.getquill.context.CanReturnMultiField
import io.getquill.context.sql._
import io.getquill.context.sql.idiom._
import io.getquill.idiom.StatementInterpolator._
import io.getquill.idiom.{ Statement, StringToken, Token }
import io.getquill.norm.ConcatBehavior
import io.getquill.norm.ConcatBehavior.NonAnsiConcat

trait OracleDialect
  extends SqlIdiom
  with QuestionMarkBindVariables
  with ConcatSupport
  with CanReturnMultiField {

  class OracleFlattenSqlQueryTokenizerHelper(q: FlattenSqlQuery)(implicit astTokenizer: Tokenizer[Ast], strategy: NamingStrategy)
    extends FlattenSqlQueryTokenizerHelper(q)(astTokenizer, strategy) {
    import q._

    override def withFrom: Statement = from match {
      case Nil =>
        stmt"$withDistinct FROM DUAL"
      case _ =>
        super.withFrom
    }
  }

  override implicit def sqlQueryTokenizer(implicit astTokenizer: Tokenizer[Ast], strategy: NamingStrategy): Tokenizer[SqlQuery] = Tokenizer[SqlQuery] {
    case q: FlattenSqlQuery =>
      new OracleFlattenSqlQueryTokenizerHelper(q).apply
    case other =>
      super.sqlQueryTokenizer.token(other)
  }

  override def concatBehavior: ConcatBehavior = NonAnsiConcat

  override def emptySetContainsToken(field: Token) = StringToken("1 <> 1")

  override protected def limitOffsetToken(query: Statement)(implicit astTokenizer: Tokenizer[Ast], strategy: NamingStrategy) =
    Tokenizer[(Option[Ast], Option[Ast])] {
      case (Some(limit), None)         => stmt"$query FETCH FIRST ${limit.token} ROWS ONLY"
      case (Some(limit), Some(offset)) => stmt"$query OFFSET ${offset.token} ROWS FETCH NEXT ${limit.token} ROWS ONLY"
      case (None, Some(offset))        => stmt"$query OFFSET ${offset.token} ROWS"
      case other                       => super.limitOffsetToken(query).token(other)
    }

  override implicit def operationTokenizer(implicit astTokenizer: Tokenizer[Ast], strategy: NamingStrategy): Tokenizer[Operation] =
    Tokenizer[Operation] {
      case BinaryOperation(a, NumericOperator.`%`, b) => stmt"MOD(${a.token}, ${b.token})"
      case other                                      => super.operationTokenizer.token(other)
    }

  override implicit def sourceTokenizer(implicit astTokenizer: Tokenizer[Ast], strategy: NamingStrategy): Tokenizer[FromContext] = Tokenizer[FromContext] {
    case QueryContext(query, alias) => stmt"(${query.token}) ${strategy.default(alias).token}"
    case other                      => super.sourceTokenizer.token(other)
  }

  override protected def tokenizeColumn(strategy: NamingStrategy, column: String, renameable: Renameable): String =
    tokenizeEscapeUnderscores(strategy, column, Some(renameable))

  override protected def tokenizeTable(strategy: NamingStrategy, table: String, renameable: Renameable): String =
    tokenizeEscapeUnderscores(strategy, table, Some(renameable))

  override protected def tokenizeColumnAlias(strategy: NamingStrategy, table: String): String =
    tokenizeEscapeUnderscores(strategy, table, None)

  private def tokenizeEscapeUnderscores(strategy: NamingStrategy, columnOrTable: String, renameable: Option[Renameable]): String =
    if (columnOrTable.startsWith("_"))
      Escape.column(columnOrTable)
    else
      renameable match {
        case Some(renameable) => renameable.fixedOr(columnOrTable)(strategy.column(columnOrTable))
        case None             => strategy.column(columnOrTable)
      }

  override def defaultAutoGeneratedToken(field: Token) = stmt"($field) VALUES (DEFAULT)"

  override def prepareForProbing(string: String) = string
}

object OracleDialect extends OracleDialect
