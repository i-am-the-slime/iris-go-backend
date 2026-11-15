module ReproInitFromJust where
import Prelude
import Data.Maybe (Maybe(..), fromJust)
import Effect (Effect)
import Effect.Console (log)
import Partial.Unsafe (unsafePartial)
-- A top-level value whose evaluation throws stops the program as it loads, before main prints.
missing :: Int
missing = unsafePartial (fromJust Nothing)
main :: Effect Unit
main = do
  log "main runs"
  log (show missing)
