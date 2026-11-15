module ReproInitEffect where
import Prelude
import Effect (Effect)
import Effect.Console (log)
import Effect.Exception (throw)
import Effect.Unsafe (unsafePerformEffect)
-- An Effect run while the module loads prints, then throws.
settings :: Int
settings = unsafePerformEffect do
  log "loading settings"
  _ <- throw "settings are missing"
  pure 1
main :: Effect Unit
main = do
  log "main runs"
  log (show settings)
