package io.getquill.ast

import io.getquill.Spec
import io.getquill.ast.Implicits._

class AstOpsSpec extends Spec {

  "+||+" - {
    "unapply" in {
      BinaryOperation(Ident("a"), BooleanOperator.`||`, Constant(true)) must matchPattern {
        case Ident(a) +||+ Constant(t) if (a == "a" && t == true) =>
      }
    }
    "apply" in {
      (Ident("a") +||+ Constant(true)) must matchPattern {
        case BinaryOperation(Ident(a), BooleanOperator.`||`, Constant(t)) if (a == "a" && t == true) =>
      }
    }
  }

  "+&&+" - {
    "unapply" in {
      BinaryOperation(Ident("a"), BooleanOperator.`&&`, Constant(true)) must matchPattern {
        case Ident(a) +&&+ Constant(t) if (a == "a" && t == true) =>
      }
    }
    "apply" in {
      (Ident("a") +&&+ Constant(true)) must matchPattern {
        case BinaryOperation(Ident(a), BooleanOperator.`&&`, Constant(t)) if (a == "a" && t == true) =>
      }
    }
  }

  "+==+" - {
    "unapply" in {
      BinaryOperation(Ident("a"), EqualityOperator.`==`, Constant(true)) must matchPattern {
        case Ident(a) +==+ Constant(t) if (a == "a" && t == true) =>
      }
    }
    "apply" in {
      (Ident("a") +==+ Constant(true)) must matchPattern {
        case BinaryOperation(Ident(a), EqualityOperator.`==`, Constant(t)) if (a == "a" && t == true) =>
      }
    }
  }

  "exist" - {
    "apply" in {
      Exist(Ident("a")) must matchPattern {
        case BinaryOperation(Ident(a), EqualityOperator.!=, NullValue) if (a == "a") =>
      }
    }
    "unapply" in {
      BinaryOperation(Ident("a"), EqualityOperator.!=, NullValue) must matchPattern {
        case Exist(Ident(a)) if (a == "a") =>
      }
    }
  }

  "empty" - {
    "apply" in {
      Empty(Ident("a")) must matchPattern {
        case BinaryOperation(Ident(a), EqualityOperator.==, NullValue) if (a == "a") =>
      }
    }
    "unapply" in {
      BinaryOperation(Ident("a"), EqualityOperator.==, NullValue) must matchPattern {
        case Empty(Ident(a)) if (a == "a") =>
      }
    }
  }

  "if exist" - {
    "apply" in {
      IfExist(Ident("a"), Ident("b"), Ident("c")) must matchPattern {
        case If(BinaryOperation(Ident(a), EqualityOperator.!=, NullValue), Ident(b), Ident(c)) if (a == "a" && b == "b" && c == "c") =>
      }
    }
    "unapply" in {
      If(BinaryOperation(Ident("a"), EqualityOperator.!=, NullValue), Ident("b"), Ident("c")) must matchPattern {
        case IfExist(Ident(a), Ident(b), Ident(c)) if (a == "a" && b == "b" && c == "c") =>
      }
    }
  }

  "if exist or null" - {
    "apply" in {
      IfExistElseNull(Ident("a"), Ident("b")) must matchPattern {
        case If(BinaryOperation(Ident(a), EqualityOperator.!=, NullValue), Ident(b), NullValue) if (a == "a" && b == "b") =>
      }
    }
    "unapply" in {
      If(BinaryOperation(Ident("a"), EqualityOperator.!=, NullValue), Ident("b"), NullValue) must matchPattern {
        case IfExistElseNull(Ident(a), Ident(b)) if (a == "a" && b == "b") =>
      }
    }
  }
}
