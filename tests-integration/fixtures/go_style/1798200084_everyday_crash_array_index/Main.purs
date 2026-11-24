module Fun.Crash.ArrayIndex where

import Prelude

import Control.Monad.Error.Class (throwError)
import Data.Array.Partial (head)
import Data.Array (unsafeIndex)
import Data.Maybe (Maybe(..), fromJust)
import Effect (Effect)
import Effect.Aff (launchAff_)
import Effect.Class (liftEffect)
import Effect.Console (log)
import Effect.Exception (throw, error)
import Partial.Unsafe (unsafePartial, unsafeCrashWith)

main :: Effect Unit
main = do
  log (show (unsafePartial (unsafeIndex [ 1, 2 ] 5)))
  log "after"
