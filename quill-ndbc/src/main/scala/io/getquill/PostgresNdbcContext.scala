package io.getquill

import com.typesafe.config.Config
import io.getquill.util.LoadConfig
import io.getquill.context.ndbc.NdbcContext
import io.trane.ndbc.DataSource

class PostgresNdbcContext[N <: NamingStrategy](dataSource: DataSource)
  extends NdbcContext[PostgresDialect, N](dataSource) {

  def this(config: NdbcContextConfig) = this(config.dataSource)
  def this(config: Config) = this(NdbcContextConfig(config))
  def this(configPrefix: String) = this(LoadConfig(configPrefix))
}
