module Fun.Crash.Throw where

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
  log "before"
  _ <- throw "uncaught boom"
  log "after"
