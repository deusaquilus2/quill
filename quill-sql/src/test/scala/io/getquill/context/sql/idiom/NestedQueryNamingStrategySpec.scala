package io.getquill.context.sql.idiom

import io.getquill.Spec
import io.getquill.context.sql.testContextEscapeElements

class NestedQueryNamingStrategySpec extends Spec { //hello

  case class Person(id: Int, name: String)

  case class Address(ownerFk: Int, street: String)

  "with escape naming strategy" - {
    import io.getquill.context.sql.testContextEscape
    import io.getquill.context.sql.testContextEscape._

    "inner aliases should not use naming strategy" in {
      val q = quote {
        query[Person].map {
          p => (p, infix"foobar".as[Int])
        }.filter(_._1.id == 1)
      }
      testContextEscape.run(q.dynamic).string mustEqual
        """SELECT p._1id, p._1name, p._2 FROM (SELECT p."id" AS _1id, p."name" AS _1name, foobar AS _2 FROM "Person" p) AS p WHERE p._1id = 1"""
    }

    "inner aliases should use naming strategy only when instructed" in {
      System.setProperty("quill.macro.log.pretty", "false")
      System.setProperty("quill.macro.log", "true")
      System.setProperty("quill.trace.enabled", "true")
      System.setProperty("quill.trace.color", "true")
      System.setProperty("quill.trace.opinion", "false")
      System.setProperty("quill.trace.ast.simple", "false")
      System.setProperty("quill.trace.types", "sql,norm,standard")

      import testContextEscapeElements._
      val q = quote {
        query[Person].map {
          p => (p, infix"foobar".as[Int])
        }.filter(_._1.id == 1)
      }
      testContextEscapeElements.run(q.dynamic).string mustEqual
        """SELECT "p"."_1id", "p"."_1name", "p"."_2" FROM (SELECT "p"."id" AS "_1id", "p"."name" AS "_1name", foobar AS "_2" FROM "Person" "p") AS "p" WHERE "p"."_1id" = 1"""
    }
  }

  "with upper naming strategy" - {
    import io.getquill.context.sql.testContextUpper
    import io.getquill.context.sql.testContextUpper._

    "inner aliases should use naming strategy" in {
      val q = quote {
        query[Person].map {
          p => (p, infix"foobar".as[Int])
        }.filter(_._1.id == 1)
      }
      testContextUpper.run(q).string mustEqual
        "SELECT p._1id, p._1name, p._2 FROM (SELECT p.ID AS _1id, p.NAME AS _1name, foobar AS _2 FROM PERSON P) AS P WHERE p._1id = 1"
    }

    "inner aliases should use naming strategy with override" in {
      val qs = quote {
        querySchema[Person]("ThePerson", _.id -> "theId", _.name -> "theName")
      }

      System.setProperty("quill.macro.log.pretty", "false")
      System.setProperty("quill.macro.log", "true")
      System.setProperty("quill.trace.enabled", "true")
      System.setProperty("quill.trace.color", "true")
      System.setProperty("quill.trace.opinion", "true")
      System.setProperty("quill.trace.ast.simple", "false")
      System.setProperty("quill.trace.types", "sql,norm,standard")

      val q = quote {
        qs.map {
          p => (p, infix"foobar".as[Int])
        }.filter(_._1.id == 1)
      }
      testContextUpper.run(q.dynamic).string mustEqual
        "SELECT p._1theId, p._1theName, p._2 FROM (SELECT p.theId AS _1theId, p.theName AS _1theName, foobar AS _2 FROM ThePerson P) AS P WHERE p._1theId = 1"
    }

    "inner aliases should use naming strategy with override - two tables" in {
      val qs = quote {
        querySchema[Person]("ThePerson", _.id -> "theId", _.name -> "theName")
      }

      val joined = quote {
        qs.join(query[Person]).on((a, b) => a.name == b.name)
      }

      val q = quote {
        joined.map { (ab) =>
          val (a, b) = ab
          (a, b, infix"foobar".as[Int])
        }.filter(_._1.id == 1)
      }
      testContextUpper.run(q).string mustEqual
        "SELECT ab._1theId, ab._1theName, ab._2id, ab._2name, ab._3 FROM (SELECT a.theId AS _1theId, a.theName AS _1theName, b.id AS _2id, b.name AS _2name, foobar AS _3 FROM ThePerson A INNER JOIN PERSON B ON a.theName = b.NAME) AS AB WHERE ab._1theId = 1"
    }

    "inner alias should nest properly in multiple levels" in {
      val q = quote {
        query[Person].map {
          p => (p, infix"foobar".as[Int])
        }.filter(_._1.id == 1).map {
          pp => (pp, infix"barbaz".as[Int])
        }.filter(_._1._1.id == 2)
      }

      testContextUpper.run(q).string mustEqual
        "SELECT p._1_1id, p._1_1name, p._1_2, p._2 FROM (SELECT p._1id AS _1_1id, p._1name AS _1_1name, p._2 AS _1_2, barbaz AS _2 FROM (SELECT p.ID AS _1id, p.NAME AS _1name, foobar AS _2 FROM PERSON P) AS P WHERE p._1id = 1) AS P WHERE p._1_1id = 2"
    }

    "inner alias should nest properly in multiple levels - with query schema" in {

      val qs = quote {
        querySchema[Person]("ThePerson", _.id -> "theId", _.name -> "theName")
      }

      val q = quote {
        qs.map {
          p => (p, infix"foobar".as[Int])
        }.filter(_._1.id == 1).map {
          pp => (pp, infix"barbaz".as[Int])
        }.filter(_._1._1.id == 2)
      }

      testContextUpper.run(q).string mustEqual
        "SELECT p._1_1theId, p._1_1theName, p._1_2, p._2 FROM (SELECT p._1theId AS _1_1theId, p._1theName AS _1_1theName, p._2 AS _1_2, barbaz AS _2 FROM (SELECT p.theId AS _1theId, p.theName AS _1theName, foobar AS _2 FROM ThePerson P) AS P WHERE p._1theId = 1) AS P WHERE p._1_1theId = 2"
    }
  }
}
