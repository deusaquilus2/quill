package io.getquill.quat

import io.getquill.ast.{ Entity, PropertyAlias }
import scala.reflect.runtime.{ universe => u }

object MakeEntity {
  def of[T: u.TypeTag](name: String, properties: List[PropertyAlias]) =
    Entity(name, properties, MakeQuat[T])
}
