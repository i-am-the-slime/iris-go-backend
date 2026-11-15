module ReproInitUnused where
import Prelude
import Effect (Effect)
import Effect.Console (log)
import Effect.Unsafe (unsafePerformEffect)
-- A top-level effect that main never references still runs when the module loads.
banner :: Unit
banner = unsafePerformEffect (log "banner")
main :: Effect Unit
main = log "main runs"
