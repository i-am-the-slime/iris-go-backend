module ReproInitCrash where
import Prelude
import Effect (Effect)
import Effect.Console (log)
import Partial.Unsafe (unsafeCrashWith)
table :: Array String
table = unsafeCrashWith "table is not ready"
main :: Effect Unit
main = do
  log "main runs"
  log (show table)
