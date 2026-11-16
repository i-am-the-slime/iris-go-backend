module ReproConsoleStreams where
import Prelude
import Effect (Effect)
import Effect.Console (clear, debug, error, group, groupCollapsed, groupEnd, info, log, time, timeEnd, timeLog, warn)
-- log, info and debug write to standard output; warn, error and the timers to standard error,
-- which the suite does not compare. A group indents the first line of each message; a collapsed
-- group prints its label without indenting, yet still ends a level.
main :: Effect Unit
main = do
  log "log"
  warn "warn"
  info "info"
  error "error"
  debug "debug"
  time "timer"
  group "outer"
  log "in outer"
  group "inner"
  log "two\nlines"
  timeLog "timer"
  groupEnd
  groupCollapsed "collapsed"
  log "after collapsed"
  groupEnd
  groupEnd
  groupEnd
  log "outside"
  timeEnd "timer"
  clear
  log "end"
