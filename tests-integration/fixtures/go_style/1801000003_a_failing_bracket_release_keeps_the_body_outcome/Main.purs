module Main where

import Prelude

import Data.Either (either)
import Effect (Effect)
import Effect.Aff (Aff, bracket, generalBracket, launchAff_, throwError, try)
import Effect.Class.Console (log)
import Effect.Exception (error, message)

main :: Effect Unit
main = launchAff_ do
  report "both fail" (bracket (pure unit) failingRelease \_ -> throwError (error "action failed"))
  report "only the release fails" (bracket (pure unit) failingRelease \_ -> pure "action succeeded")
  report "general, both fail" (generalBracket (pure unit) failingConditions \_ -> throwError (error "action failed"))
  report "general, only the release fails" (generalBracket (pure unit) failingConditions \_ -> pure "action succeeded")
  where
  failingRelease _ = throwError (error "release failed")
  failingConditions =
    { killed: \_ _ -> throwError (error "killed release failed")
    , failed: \_ _ -> throwError (error "failed release failed")
    , completed: \_ _ -> throwError (error "completed release failed")
    }

report :: String -> Aff String -> Aff Unit
report label action = do
  outcome <- try action
  log (label <> ": " <> either message identity outcome)
