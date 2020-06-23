package io.getquill

/**
 * Convenience API that allows construction of a Quat using `Quat.from[T]`
 */
package object quat {

  def quatOf[T: scala.reflect.runtime.universe.TypeTag] = MakeQuat.of[T]
}
