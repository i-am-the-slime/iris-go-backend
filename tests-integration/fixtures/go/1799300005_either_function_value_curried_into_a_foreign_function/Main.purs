module Main where

import Prelude

import Data.Either (Either(..))
import Effect (Effect)
import Effect.Uncurried (runEffectFn3)
import Journal (log)
import Outcome (outcomeImpl)

failedWith :: Int -> String -> Either String Int
failedWith code message = Left (message <> " (code " <> show code <> ")")

main :: Effect Unit
main = do
  finished <- runEffectFn3 outcomeImpl failedWith (Right 1) true
  log (show finished)
  broken <- runEffectFn3 outcomeImpl failedWith (Right 1) false
  log (show broken)
