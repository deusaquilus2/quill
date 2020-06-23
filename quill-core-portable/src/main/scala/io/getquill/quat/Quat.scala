package io.getquill.quat

// This represents a simplified Sql-Type. Since it applies to all dialects, it is called
// Quill-Application-Type hence Quat.
sealed trait Quat {
  def applyRenames: Quat = this
  def withRenames(renames: List[(String, String)]): Quat
  def renames: List[(String, String)] = List()

  // Roughly speaking, is this a super-type of the inner type
  def canReduceTo(other: Quat): Boolean = {
    (this, other) match {
      case (Quat.Value, Quat.Value)           => true
      case (a: Quat.Product, b: Quat.Product) => a == b
      case (Quat.Null, Quat.Product(_)) =>
        false // Null is most specific subtype so can't replace with a supertype of it
      case (Quat.Product(_), Quat.Null) =>
        true
      case (Quat.Value, Quat.Null) => true
      case (_, _)                  => false
    }
  }

  //  def reduceTo(other: Quat): Quat = {
  //    (this, other) match {
  //      case (Quat.Value, Quat.Value) => Quat.Value
  //      case (a: Quat.Product, b: Quat.Product) => a
  //      case (Quat.Null, Quat.Product(_)) => false // Null is most specific subtype so can't replace with a supertype of it
  //      case (Quat.Product(_), Quat.Null) => true
  //      case (Quat.Value, Quat.Null) => true
  //      case (_, _) => false
  //    }
  //  }

  def shortString: String = this match {
    case Quat.Product(fields) => s"CC(${
      fields.map {
        case (k, v) => k + (v match {
          case Quat.Value => ""
          case other      => ":" + other.shortString
        })
      }.mkString(",")
    })${
      (this.renames match {
        case Nil   => ""
        case other => s"[${other.map { case (k, v) => k + "->" + v }.mkString(",")}]"
      })
    }"
    case Quat.Value      => "V"
    case Quat.Null       => "N"
    case Quat.Error(msg) => s"QError(${msg.take(20)})"
  }

  def lookup(path: String): Quat = (this, path) match {
    case (cc @ Quat.Product(fields), fieldName) =>
      fields.find(_._1 == fieldName).headOption.map(_._2).getOrElse(Quat.Error(s"The field ${fieldName} does not exist in the SQL-level ${cc}")) // TODO Quat does this not match in certain cases? Which ones?
    case (Quat.Value, fieldName) =>
      Quat.Error(s"The field ${fieldName} does not exist in an SQL-level leaf-node") // TODO Quat is there a case where we're putting a property on a entity which is actually a value?
    case (Quat.Null, fieldName) =>
      Quat.Error(s"The field ${fieldName} cannot be looked up from a SQL-level null node") // TODO Quat is there a case where we're putting a property on a entity which is actually a value?
    case (Quat.Error(msg), _) => Quat.Error(s"${msg}. Also tried to lookup ${path} from node.")
  }
  def lookup(list: List[String]): Quat =
    list match {
      case head :: tail => this.lookup(head).lookup(tail)
      case Nil          => this
    }

  /** Rename a property of a Quat.Tuple or Quat.CaseClass. Optionally can specify a new Quat to change the property to. */
  def stashRename(property: String, newProperty: String, newQuat: Option[Quat] = None): Quat = {
    // sanity check does the property exist in the first place
    this.lookup(property) match {
      case e: Quat.Error => e
      case _ => {
        // TODO Quat, test quat changes with a tuple property rename
        (this, property, newProperty) match {
          case (cc: Quat.Product, property, newProperty) =>
            cc.fields.find(_._1 == property) match {
              case Some(_) =>
                val newFields =
                  cc.fields.map {
                    case (field, quat) => if (field == property) (field, newQuat.getOrElse(quat)) else (field, quat)
                  }
                Quat.Product.WithRenames(newFields, cc.renames :+ ((property, newProperty)))

              case None =>
                cc
            }
          case (Quat.Value, _, _) => Quat.Error(s"Cannot replace property ${property} with ${newProperty} on a Value SQL-level type")
          case _                  => Quat.Error(s"Invalid state reached for ${this.shortString}, ${property}, ${newProperty}")
        }
      }
    }
  }

  def stashRename(path: List[String], newEndProperty: String): Quat = {
    path match {
      case Nil => // do nothing
        this

      case head :: Nil =>
        this.stashRename(head, newEndProperty)

      case head :: tail =>
        val child = this.lookup(head)
        val newChild = child.stashRename(tail, newEndProperty)
        this.stashRename(head, head, Some(newChild))
    }
  }

}

object Quat {
  object TupleIndex {
    def is(s: String): Boolean = unapply(s).isDefined
    def unapply(s: String): Option[Int] =
      if (s.matches("_[0-9]*"))
        Some(s.drop(1).toInt - 1)
      else
        None
  }

  case class Product(fields: List[(String, Quat)]) extends Quat {
    override def toString: String = s"Quat.Product(${fields.map { case (k, v) => s"${k}:${v}" }.mkString(", ")})"
    override def withRenames(renames: List[(String, String)]) =
      Product.WithRenames(fields, renames)
    /**
     * Rename the properties and reset renames to empty.
     * An interesting idea would be not to clear
     * the renames at the end but rather keep them around until the SqlQuery phase wherein we could potentially
     * create SQL aliases not based on the renamed properties by based on the original property name.
     */
    override def applyRenames = {
      val newFields = fields.map {
        case (f, q) =>
          // Rename properties of this quat and rename it's children recursively
          val newKey = renames.find(_._1 == f).map(_._2).getOrElse(f)
          val newValue = q.applyRenames
          (newKey, newValue)
      }
      Product(newFields)
    }
  }
  object Product {
    def apply(fields: List[(String, Quat)]) = new Quat.Product(fields)
    def unapply(p: Quat.Product): Some[(List[(String, Quat)])] = Some(p.fields)

    /**
     * Add staged renames to the Quat. Note that renames should
     * explicit NOT be counted as part of the Type indicated by the Quat
     * since it is typical to beta reduce a Quat without renames to a Quat with them
     * (see `PropagateRenames` for more detail)
     */
    object WithRenames {
      def apply(fields: List[(String, Quat)], theRenames: List[(String, String)]) =
        new Product(fields) {
          override def renames: List[(String, String)] = theRenames
        }
      def unapply(p: Quat.Product) =
        Some((p.fields, p.renames))
    }
  }
  object Tuple {
    def apply(fields: Quat*): Quat.Product = apply(fields.toList)
    def apply(fields: List[Quat]): Quat.Product = new Quat.Product(fields.zipWithIndex.map { case (f, i) => (s"_${i + 1}", f) })
  }
  case object Null extends Quat {
    override def withRenames(renames: List[(String, String)]) = this
    override def toString: String = "N"
  }
  object Value extends Quat {

    /** Should not be able to rename properties on a value node, turns into a error of the array is not null */
    override def withRenames(renames: List[(String, String)]) =
      renames match {
        case Nil => this
        case _   => Quat.Error(s"Renames ${renames} cannot be applied to a value SQL-level type")
      }

    override def toString: String = "QV"
  }
  case class Error(msg: String) extends Quat {
    override def withRenames(renames: List[(String, String)]): Quat = this
  }
}
