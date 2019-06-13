package io.getquill.context.sql

import io.getquill.Spec
import io.getquill.context.sql.testContext._
import io.getquill.Literal

class SqlQuerySpec extends Spec {

  implicit val naming = new Literal {}

  "transforms the ast into a flatten sql-like structure" - {

    "inner join query" in {
      val q = quote {
        for {
          a <- qr1
          b <- qr2 if (a.s != null && b.i > a.i)
        } yield {
          (a.i, b.i)
        }
      }
      testContext.run(q).string mustEqual
        "SELECT a.i, b.i FROM TestEntity a, TestEntity2 b WHERE a.s IS NOT NULL AND b.i > a.i"
    }

    "outer join query" in {
      val q = quote {
        qr1.leftJoin(qr2).on((a, b) => a.s != null && b.i > a.i)
      }
      testContext.run(q).string mustEqual
        "SELECT a.s, a.i, a.l, a.o, b.s, b.i, b.l, b.o FROM TestEntity a LEFT JOIN TestEntity2 b ON a.s IS NOT NULL AND b.i > a.i"
    }

    "join + map + filter" - {
      "regular" in {
        val q = quote {
          qr1
            .leftJoin(qr2)
            .on((a, b) => a.i == b.i)
            .map(t => (t._1.i, t._2.map(_.i)))
            .filter(_._2.forall(_ == 1))
        }
        testContext.run(q).string mustEqual
          "SELECT a.i, b.i FROM TestEntity a LEFT JOIN TestEntity2 b ON a.i = b.i WHERE b.i IS NULL OR b.i = 1"
      }
      "null-checked" in {
        val q = quote {
          qr1
            .leftJoin(qr2)
            .on((a, b) => a.i == b.i)
            .map(t => (t._1.i, t._2.map(_.s)))
            .filter(_._2.forall(v => if (v == "value") true else false))
        }
        testContext.run(q).string mustEqual
          "SELECT a.i, b.s FROM TestEntity a LEFT JOIN TestEntity2 b ON a.i = b.i WHERE b.s IS NULL OR b.s IS NOT NULL AND CASE WHEN b.s = 'value' THEN true ELSE false END"
      }
    }

    "nested join" in {
      val q = quote {
        qr1.leftJoin(qr2).on {
          case (a, b) =>
            a.i == b.i
        }.filter {
          case (a, b) =>
            b.map(_.l).contains(3L)
        }.leftJoin(qr3).on {
          case ((a, b), c) =>
            b.map(_.i).contains(a.i) && b.map(_.i).contains(c.i)
        }
      }
      testContext.run(q).string mustEqual
        "SELECT x02._1s, x02._1i, x02._1l, x02._1o, x02._2s, x02._2i, x02._2l, x02._2o, x12.s, x12.i, x12.l, x12.o FROM (SELECT x01.s AS _1s, x01.l AS _1l, x01.o AS _1o, x01.i AS _1i, x11.i AS _2i, x11.o AS _2o, x11.l AS _2l, x11.s AS _2s FROM TestEntity x01 LEFT JOIN TestEntity2 x11 ON x01.i = x11.i WHERE x11.l = 3) AS x02 LEFT JOIN TestEntity3 x12 ON x02._2i = x02._1i AND x02._2i = x12.i"
    }

    "flat outer join" in {
      val q = quote {
        for {
          e1 <- qr1
          e2 <- qr2.leftJoin(e2 => e2.i == e1.i)
        } yield (e1.i, e2.map(e => e.i))
      }
      testContext.run(q.dynamic).string mustEqual
        "SELECT e1.i, e2.i FROM TestEntity e1 LEFT JOIN TestEntity2 e2 ON e2.i = e1.i"
    }

    "value query" - {
      "operation" in {
        val q = quote {
          qr1.map(t => t.i).contains(1)
        }
        testContext.run(q).string mustEqual
          "SELECT 1 IN (SELECT t.i FROM TestEntity t)"
      }
      "simple value" in {
        val q = quote(1)
        testContext.run(q).string mustEqual
          "SELECT 1"
      }
    }

    "raw queries with infix" - {
      "using tuples" in {
        val q = quote {
          infix"""SELECT t.s AS "_1", t.i AS "_2" FROM TestEntity t""".as[Query[(String, Int)]]
        }
        testContext.run(q).string mustEqual
          """SELECT x._1, x._2 FROM (SELECT t.s AS "_1", t.i AS "_2" FROM TestEntity t) AS x"""
      }
      "using single value" in {
        val q = quote {
          infix"""SELECT t.i FROM TestEntity t""".as[Query[Int]]
        }
        testContext.run(q).string mustEqual
          """SELECT x.* FROM (SELECT t.i FROM TestEntity t) AS x"""
      }
    }

    "nested infix query" - {
      "as source" in {
        val q = quote {
          infix"SELECT * FROM TestEntity".as[Query[TestEntity]].filter(t => t.i == 1)
        }
        testContext.run(q).string mustEqual
          "SELECT t.s, t.i, t.l, t.o FROM (SELECT * FROM TestEntity) AS t WHERE t.i = 1"
      }
      "fails if used as the flatMap body" in {
        val q = quote {
          qr1.flatMap(a => infix"SELECT * FROM TestEntity2 t where t.s = ${a.s}".as[Query[TestEntity2]])
        }
        val e = intercept[IllegalStateException] {
          SqlQuery(q.ast)
        }
      }
    }
    "sorted query" - {
      "with map" in {
        val q = quote {
          qr1.sortBy(t => t.s).map(t => t.s)
        }
        testContext.run(q).string mustEqual
          "SELECT t.s FROM TestEntity t ORDER BY t.s ASC NULLS FIRST"
      }
      "with filter" in {
        val q = quote {
          qr1.filter(t => t.s == "s").sortBy(t => t.s).map(t => (t.i))
        }
        testContext.run(q).string mustEqual
          "SELECT t.i FROM TestEntity t WHERE t.s = 's' ORDER BY t.s ASC NULLS FIRST"
      }
      "with outer filter" in {
        val q = quote {
          qr1.sortBy(t => t.s).filter(t => t.s == "s").map(t => t.s)
        }
        testContext.run(q).string mustEqual
          "SELECT t.s FROM TestEntity t WHERE t.s = 's' ORDER BY t.s ASC NULLS FIRST"
      }
      "with flatMap" in {
        val q = quote {
          qr1.sortBy(t => t.s).flatMap(t => qr2.map(t => t.s))
        }
        testContext.run(q).string mustEqual
          "SELECT t1.s FROM (SELECT t.* FROM TestEntity t ORDER BY t.s ASC NULLS FIRST) AS t, TestEntity2 t1"
      }
      "tuple criteria" - {
        "single ordering" in {
          val q = quote {
            qr1.sortBy(t => (t.s, t.i))(Ord.asc).map(t => t.s)
          }
          testContext.run(q).string mustEqual
            "SELECT t.s FROM TestEntity t ORDER BY t.s ASC, t.i ASC"
        }
        "ordering per column" in {
          val q = quote {
            qr1.sortBy(t => (t.s, t.i))(Ord(Ord.asc, Ord.desc)).map(t => t.s)
          }
          testContext.run(q).string mustEqual
            "SELECT t.s FROM TestEntity t ORDER BY t.s ASC, t.i DESC"
        }
      }
      "multiple sortBy" in {
        val q = quote {
          qr1.sortBy(t => (t.s, t.i)).sortBy(t => t.l).map(t => t.s)
        }
        testContext.run(q).string mustEqual
          "SELECT t.s FROM (SELECT t.l, t.s FROM TestEntity t ORDER BY t.s ASC NULLS FIRST, t.i ASC NULLS FIRST) AS t ORDER BY t.l ASC NULLS FIRST"
      }
      "expression" - {
        "neg" in {
          val q = quote {
            qr1.sortBy(t => -t.i)(Ord.desc)
          }
          testContext.run(q).string mustEqual
            "SELECT t.s, t.i, t.l, t.o FROM TestEntity t ORDER BY - (t.i) DESC"
        }
        "add" in {
          val q = quote {
            qr1.sortBy(t => t.l - t.i)
          }
          testContext.run(q).string mustEqual
            "SELECT t.s, t.i, t.l, t.o FROM TestEntity t ORDER BY (t.l - t.i) ASC NULLS FIRST"
        }
      }
      "after flatMap" in {
        val q = quote {
          (for {
            a <- qr1
            b <- qr2 if a.i == b.i
          } yield {
            (a.s, b.s)
          })
            .sortBy(_._2)(Ord.desc)
        }
        testContext.run(q).string mustEqual
          "SELECT b._1, b._2 FROM (SELECT b.s AS _2, a.s AS _1 FROM TestEntity a, TestEntity2 b WHERE a.i = b.i) AS b ORDER BY b._2 DESC"
      }
      "fails if the sortBy criteria is malformed" in {
        case class Test(a: (Int, Int))
        implicit val o: Ordering[TestEntity] = null
        val q = quote {
          query[Test].sortBy(_.a)(Ord(Ord.asc, Ord.desc))
        }
        val e = intercept[IllegalStateException] {
          SqlQuery(q.ast)
        }
      }
    }
    "grouped query" - {
      "simple" in {
        val q = quote {
          qr1.groupBy(t => t.i).map(t => t._1)
        }
        testContext.run(q).string mustEqual
          "SELECT t.i FROM TestEntity t GROUP BY t.i"
      }
      "nested" in {
        val q = quote {
          qr1.groupBy(t => t.i).map(t => t._1).flatMap(t => qr2)
        }
        testContext.run(q).string mustEqual
          "SELECT x.s, x.i, x.l, x.o FROM (SELECT t.i FROM TestEntity t GROUP BY t.i) AS t, TestEntity2 x"
      }
      "without map" in {
        val q = quote {
          qr1.groupBy(t => t.i)
        }
        val e = intercept[IllegalStateException] {
          SqlQuery(q.ast)
        }
      }
      "tuple" in {
        val q = quote {
          qr1.groupBy(t => (t.i, t.l)).map(t => t._1)
        }
        testContext.run(q).string mustEqual
          "SELECT t.i, t.l FROM TestEntity t GROUP BY t.i, t.l"
      }
      "aggregated" - {
        "simple" in {
          val q = quote {
            qr1.groupBy(t => t.i).map {
              case (i, entities) => (i, entities.size)
            }
          }
          testContext.run(q).string mustEqual
            "SELECT t.i, COUNT(*) FROM TestEntity t GROUP BY t.i"
        }
        "mapped" in {
          val q = quote {
            qr1.groupBy(t => t.i).map {
              case (i, entities) => (i, entities.map(_.l).max)
            }
          }
          testContext.run(q).string mustEqual
            "SELECT t.i, MAX(t.l) FROM TestEntity t GROUP BY t.i"
        }
        "distinct" in {
          val q = quote {
            qr1.groupBy(t => t.s).map {
              case (s, entities) => (s, entities.map(_.i).distinct.size)
            }
          }
          testContext.run(q).string mustEqual
            "SELECT t.s, COUNT(DISTINCT t.i) FROM TestEntity t GROUP BY t.s"
        }
      }
      "with map" - {
        "not nested" in {
          val q = quote {
            qr1.join(qr2).on((a, b) => a.s == b.s)
              .groupBy(t => t._2.i)
              .map {
                case (i, l) =>
                  (i, l.map(_._1.i).sum)
              }
          }
          testContext.run(q).string mustEqual
            "SELECT b.i, SUM(a.i) FROM TestEntity a INNER JOIN TestEntity2 b ON a.s = b.s GROUP BY b.i"
        }
        "nested" in {
          val q = quote {
            qr1.join(qr2).on((a, b) => a.s == b.s)
              .nested
              .groupBy(t => t._2.i)
              .map {
                case (i, l) =>
                  (i, l.map(_._1.i).sum)
              }
          }
          testContext.run(q).string mustEqual
            "SELECT t._2i, SUM(t._1i) FROM (SELECT a.i AS _1i, b.i AS _2i FROM TestEntity a INNER JOIN TestEntity2 b ON a.s = b.s) AS t GROUP BY t._2i"
        }
      }
    }
    "aggregated query" in {
      val q = quote {
        qr1.map(t => t.i).max
      }
      testContext.run(q).string mustEqual
        "SELECT MAX(t.i) FROM TestEntity t"
    }
    "aggregated query multiple select" in {
      val q = quote {
        qr1.map(t => t.i -> t.s).size
      }
      testContext.run(q).string mustEqual
        "SELECT COUNT(*) FROM (SELECT t.i, t.s FROM TestEntity t) AS x"
    }

    "distinct" - {
      "distinct query" in {
        val q = quote {
          qr1.map(t => t.i).distinct
        }
        testContext.run(q).string mustEqual
          "SELECT DISTINCT t.i FROM TestEntity t"
      }
      "with map" in {
        val q = quote {
          qr1.map(t => t.i).distinct.map(t => 1)
        }
        testContext.run(q).string mustEqual
          "SELECT 1 FROM (SELECT DISTINCT t.i FROM TestEntity t) AS t"
      }

      "with map inside join" in {
        val q = quote {
          qr1
            .join(
              qr2
                .map(q2 => q2.i)
                .distinct
            )
            .on(_.i == _)
        }
        testContext.run(q).string mustEqual
          "SELECT x15.s, x15.i, x15.l, x15.o, x16.* FROM TestEntity x15 INNER JOIN (SELECT DISTINCT i AS i FROM TestEntity2 q2) AS q21 ON x15.i = q21.i"
      }

      // If you look inside BetaReduction, you will see that tuple values that are the same are collapsed via 'distinct'.
      // In this case, use different values that do not allow this to happen
      "with map query inside join with non-distinct tuple" in {
        val q = quote {
          qr1
            .join(
              qr2
                .map(q2 => (q2.i, q2.l))
                .distinct
            )
            .on(_.i == _._1)
        }
        testContext.run(q).string mustEqual
          "SELECT x17.s, x17.i, x17.l, x17.o, x18._1, x18._2 FROM TestEntity x17 INNER JOIN (SELECT DISTINCT q2.i AS _1, q2.l AS _2 FROM TestEntity2 q2) AS x18 ON x17.i = x18._1"
      }

      "with map query inside join with non-distinct tuple with operation" in {
        val q = quote {
          qr1
            .join(
              qr2
                .map(q2 => (q2.i + 1, q2.l))
                .distinct
            )
            .on(_.i == _._1)
        }
        testContext.run(q).string mustEqual
          "SELECT x19.s, x19.i, x19.l, x19.o, x20._1, x20._2 FROM TestEntity x19 INNER JOIN (SELECT DISTINCT q2.i + 1 AS _1, q2.l AS _2 FROM TestEntity2 q2) AS x20 ON x19.i = x20._1"
      }

      "with map query inside join with case class" in {
        case class IntermediateRecord(one: Int, two: Long)
        val q = quote {
          qr1
            .join(
              qr2
                .map(q2 => IntermediateRecord(q2.i, q2.l))
                .distinct
            )
            .on(_.i == _.one)
        }
        testContext.run(q).string mustEqual
          "SELECT x21.s, x21.i, x21.l, x21.o, x22.one, x22.two FROM TestEntity x21 INNER JOIN (SELECT DISTINCT q2.i AS one, q2.l AS two FROM TestEntity2 q2) AS x22 ON x21.i = x22.one"
      }

      "with map query inside join with case class and operation" in {
        case class IntermediateRecord(one: Int, two: Long)
        val q = quote {
          qr1
            .join(
              qr2
                .map(q2 => IntermediateRecord(q2.i, q2.l))
                .distinct
            )
            .on(_.i == _.one)
        }
        testContext.run(q).string mustEqual
          "SELECT x23.s, x23.i, x23.l, x23.o, x24.one, x24.two FROM TestEntity x23 INNER JOIN (SELECT DISTINCT q2.i AS one, q2.l AS two FROM TestEntity2 q2) AS x24 ON x23.i = x24.one"
      }

      "sort with distinct immediately afterward" in {
        val q = quote {
          qr1
            .join(qr2)
            .on(_.i == _.i)
            .distinct
            .sortBy(_._1.i)(Ord.desc)
        }
        testContext.run(q).string mustEqual
          "SELECT x27._1s, x27._1i, x27._1l, x27._1o, x27._2s, x27._2i, x27._2l, x27._2o FROM (SELECT DISTINCT x25.l AS _1l, x25.o AS _1o, x25.i AS _1i, x25.s AS _1s, x26.s AS _2s, x26.i AS _2i, x26.o AS _2o, x26.l AS _2l FROM TestEntity x25 INNER JOIN TestEntity2 x26 ON x25.i = x26.i ORDER BY x25.i DESC) AS x27"
      }
    }

    "nested where" in {
      val q = quote {
        qr4.filter(t => t.i == 1).nested.filter(t => t.i == 2)
      }
      testContext.run(q).string mustEqual
        "SELECT t.i FROM (SELECT t.i FROM TestEntity4 t WHERE t.i = 1) AS t WHERE t.i = 2"
    }

    "limited query" - {
      "simple" in {
        val q = quote {
          qr1.take(10)
        }
        testContext.run(q).string mustEqual
          "SELECT x.s, x.i, x.l, x.o FROM TestEntity x LIMIT 10"
      }
      "nested" in {
        val q = quote {
          qr1.take(10).flatMap(a => qr2)
        }
        testContext.run(q).string mustEqual
          "SELECT x.s, x.i, x.l, x.o FROM (SELECT x.* FROM TestEntity x LIMIT 10) AS a, TestEntity2 x"
      }
      "with map" in {
        val q = quote {
          qr1.take(10).map(t => t.s)
        }
        testContext.run(q).string mustEqual
          "SELECT t.s FROM TestEntity t LIMIT 10"
      }
      "multiple limits" in {
        val q = quote {
          qr1.take(1).take(10)
        }
        testContext.run(q).string mustEqual
          "SELECT x.s, x.i, x.l, x.o FROM (SELECT x.s, x.i, x.l, x.o FROM TestEntity x LIMIT 1) AS x LIMIT 10"
      }
    }
    "offset query" - {
      "simple" in {
        val q = quote {
          qr1.drop(10)
        }
        testContext.run(q).string mustEqual
          "SELECT x.s, x.i, x.l, x.o FROM TestEntity x OFFSET 10"
      }
      "nested" in {
        val q = quote {
          qr1.drop(10).flatMap(a => qr2)
        }
        testContext.run(q).string mustEqual
          "SELECT x.s, x.i, x.l, x.o FROM (SELECT x.* FROM TestEntity x OFFSET 10) AS a, TestEntity2 x"
      }
      "with map" in {
        val q = quote {
          qr1.drop(10).map(t => t.s)
        }
        testContext.run(q).string mustEqual
          "SELECT t.s FROM TestEntity t OFFSET 10"
      }
      "multiple offsets" in {
        val q = quote {
          qr1.drop(1).drop(10)
        }
        testContext.run(q).string mustEqual
          "SELECT x.s, x.i, x.l, x.o FROM (SELECT x.s, x.i, x.l, x.o FROM TestEntity x OFFSET 1) AS x OFFSET 10"
      }
    }
    "limited and offset query" - {
      "simple" in {
        val q = quote {
          qr1.drop(10).take(11)
        }
        testContext.run(q).string mustEqual
          "SELECT x.s, x.i, x.l, x.o FROM TestEntity x LIMIT 11 OFFSET 10"
      }
      "nested" in {
        val q = quote {
          qr1.drop(10).take(11).flatMap(a => qr2)
        }
        testContext.run(q).string mustEqual
          "SELECT x.s, x.i, x.l, x.o FROM (SELECT x.* FROM TestEntity x LIMIT 11 OFFSET 10) AS a, TestEntity2 x"
      }
      "multiple" in {
        val q = quote {
          qr1.drop(1).take(2).drop(3).take(4)
        }
        testContext.run(q).string mustEqual
          "SELECT x.s, x.i, x.l, x.o FROM (SELECT x.s, x.i, x.l, x.o FROM TestEntity x LIMIT 2 OFFSET 1) AS x LIMIT 4 OFFSET 3"
      }
      "take.drop" in {
        val q = quote {
          qr1.take(1).drop(2)
        }
        testContext.run(q).string mustEqual
          "SELECT x.s, x.i, x.l, x.o FROM (SELECT x.s, x.i, x.l, x.o FROM TestEntity x LIMIT 1) AS x OFFSET 2"
      }
      "for comprehension" - {
        val q = quote(for {
          q1 <- qr1
          q2 <- qr2 if q1.i == q2.i
        } yield (q1.i, q2.i, q1.s, q2.s))

        "take" in {
          testContext.run(q.take(3)).string mustEqual
            "SELECT q1.i, q2.i, q1.s, q2.s FROM TestEntity q1, TestEntity2 q2 WHERE q1.i = q2.i LIMIT 3"
        }
        "drop" in {
          testContext.run(q.drop(3)).string mustEqual
            "SELECT q1.i, q2.i, q1.s, q2.s FROM TestEntity q1, TestEntity2 q2 WHERE q1.i = q2.i OFFSET 3"
        }
      }
    }
    "set operation query" - {
      "union" in {
        val q = quote {
          qr1.union(qr1)
        }
        testContext.run(q).string mustEqual
          "SELECT x.s, x.i, x.l, x.o FROM ((SELECT x.s, x.i, x.l, x.o FROM TestEntity x) UNION (SELECT x.s, x.i, x.l, x.o FROM TestEntity x)) AS x"
      }
      "unionAll" in {
        val q = quote {
          qr1.unionAll(qr1)
        }
        testContext.run(q).string mustEqual
          "SELECT x.s, x.i, x.l, x.o FROM ((SELECT x.s, x.i, x.l, x.o FROM TestEntity x) UNION ALL (SELECT x.s, x.i, x.l, x.o FROM TestEntity x)) AS x"
      }
    }
    "unary operation query" - {
      "nonEmpty" in {
        val q = quote {
          qr1.nonEmpty
        }
        testContext.run(q).string mustEqual
          "SELECT EXISTS (SELECT x.* FROM TestEntity x)"
      }
      "isEmpty" in {
        val q = quote {
          qr1.isEmpty
        }
        testContext.run(q).string mustEqual
          "SELECT NOT EXISTS (SELECT x.* FROM TestEntity x)"
      }
    }
    "aggregated and mapped query" in {
      val q = quote {
        (for {
          q1 <- qr1
          q2 <- qr2
        } yield {
          q2.i
        }).min
      }
      testContext.run(q).string mustEqual
        "SELECT MIN(q2.i) FROM TestEntity q1, TestEntity2 q2"
    }
    "nested" - {
      "pointless nesting" in {
        val q = quote {
          qr4.nested
        }
        testContext.run(q).string mustEqual "SELECT x.i FROM (SELECT x.i FROM TestEntity4 x) AS x"
        // not normalized
        SqlQuery(q.ast).toString mustEqual "SELECT x.* FROM (SELECT x.* FROM TestEntity4 x) AS x"
      }
      "pointless nesting of single yielding element" in {
        val q = quote {
          qr1.map(x => x.i).nested
        }
        testContext.run(q).string mustEqual "SELECT x.i FROM (SELECT x.i FROM TestEntity x) AS x"
      }
      "pointless nesting in for-comp of single yielding element" in {
        val q = quote {
          (for {
            a <- qr1
            b <- qr2
          } yield a.i).nested
        }
        testContext.run(q).string mustEqual "SELECT x.* FROM (SELECT a.i FROM TestEntity a, TestEntity2 b) AS x"
      }
      "mapped" in {
        val q = quote {
          qr1.nested.map(t => t.i)
        }
        testContext.run(q).string mustEqual
          "SELECT t.i FROM (SELECT x.i FROM TestEntity x) AS t"
      }
      "filter + map" in {
        val q = quote {
          qr1.filter(t => t.i == 1).nested.map(t => t.i)
        }
        testContext.run(q).string mustEqual
          "SELECT t.i FROM (SELECT t.i FROM TestEntity t WHERE t.i = 1) AS t"
      }
    }

    "queries using options" - {
      case class Entity(id: Int, s: String, o: Option[String], fk: Int, io: Option[Int])
      case class EntityA(id: Int, s: String, o: Option[String])
      case class EntityB(id: Int, s: String, o: Option[String])

      val e = quote(query[Entity])
      val ea = quote(query[EntityA])
      val eb = quote(query[EntityB])

      "flatten in left join" in {
        val q = quote {
          e.leftJoin(ea).on((e, a) => e.fk == a.id).map(_._2.map(_.o).flatten)
        }
        testContext.run(q).string mustEqual
          "SELECT a.o FROM Entity e LEFT JOIN EntityA a ON e.fk = a.id"
      }

      "flatMap in left join" in {
        val q = quote {
          e.leftJoin(ea).on((e, a) => e.fk == a.id).map(_._2.flatMap(_.o))
        }
        testContext.run(q).string mustEqual
          "SELECT a.o FROM Entity e LEFT JOIN EntityA a ON e.fk = a.id"
      }

      "flatMap in left join with getOrElse" in {
        val q = quote {
          e.leftJoin(ea).on((e, a) => e.fk == a.id).map(_._2.flatMap(_.o).getOrElse("alternative"))
        }
        testContext.run(q).string mustEqual
          "SELECT CASE WHEN a.o IS NOT NULL THEN a.o ELSE 'alternative' END FROM Entity e LEFT JOIN EntityA a ON e.fk = a.id"
      }

      "getOrElse should not produce null check for integer" in {
        val q = quote {
          e.map(em => em.io.map(_ + 1).getOrElse(2))
        }
        testContext.run(q).string mustEqual
          "SELECT CASE WHEN (em.io + 1) IS NOT NULL THEN em.io + 1 ELSE 2 END FROM Entity em"
      }

      "getOrElse should not produce null check for conditional" in {
        val q = quote {
          e.map(em => em.o.map(v => if (v == "value") "foo" else "bar").getOrElse("baz"))
        }
        testContext.run(q).string mustEqual
          "SELECT CASE WHEN em.o IS NOT NULL AND CASE WHEN em.o = 'value' THEN 'foo' ELSE 'bar' END IS NOT NULL THEN CASE WHEN em.o = 'value' THEN 'foo' ELSE 'bar' END ELSE 'baz' END FROM Entity em"
      }
    }

    "case class queries" - {
      case class TrivialEntity(str: String)

      "in single join" in {
        val q = quote {
          for {
            a <- qr1
            b <- qr2 if (b.i > a.i)
          } yield {
            TrivialEntity(b.s)
          }
        }
        testContext.run(q).string mustEqual
          "SELECT b.s FROM TestEntity a, TestEntity2 b WHERE b.i > a.i"
      }

      "in union" in {
        val q = quote {
          qr1.map(q => TrivialEntity(q.s)) ++ qr1.map(q => TrivialEntity(q.s))
        }
        testContext.run(q).string mustEqual
          "SELECT x.str FROM ((SELECT q.s AS str FROM TestEntity q) UNION ALL (SELECT q1.s AS str FROM TestEntity q1)) AS x"
      }

      "in union same field name" in {
        case class TrivialEntitySameField(s: String)

        val q = quote {
          qr1.map(q => TrivialEntitySameField(q.s)) ++ qr1.map(q => TrivialEntitySameField(q.s))
        }
        testContext.run(q).string mustEqual
          "SELECT x.s FROM ((SELECT q.s AS s FROM TestEntity q) UNION ALL (SELECT q1.s AS s FROM TestEntity q1)) AS x"
      }
    }
  }

  "SqlQuery" - {
    import io.getquill.ast._

    "toString" in {
      SqlQuery(qr4.ast).toString mustBe "SELECT x.* FROM TestEntity4 x"
    }
    "catch invalid" in {
      intercept[IllegalStateException](SqlQuery(Ident("i"))).getMessage must startWith("Query not properly normalized.")
    }
  }
}
