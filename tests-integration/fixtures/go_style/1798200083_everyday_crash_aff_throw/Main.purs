module Fun.Crash.AffThrow where

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
  launchAff_ do
    liftEffect (log "in aff")
    _ <- throwError (error "aff uncaught")
    liftEffect (log "after")
  log "main continues"
