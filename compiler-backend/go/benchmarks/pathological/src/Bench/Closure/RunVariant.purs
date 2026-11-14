module Bench.Closure.RunVariant where

import Prelude

import Bench.Harness (benchmark)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Run (Run, extract)
import Run.Except (EXCEPT, catch, runExcept, throw)
import Run.Reader (READER, ask, runReader)
import Run.State (STATE, get, modify, runState)
import Type.Row (type (+))
import Data.Either (Either(..))

hypothesis :: String
hypothesis = "Run dispatches each effect through a Variant (label string + unsafeCoerce) inside a Free monad: closures, boxing and string compares per step"

main :: Effect Unit
main = benchmark { size: 30000, workload }

workload :: Int -> String
workload n = case extract (runExcept (runReader 3 (runState 0 (loop 0)))) of
  Right (state /\ result) -> show state <> " " <> show result
  Left message -> message
  where
  loop :: Int -> Run (STATE Int + READER Int + EXCEPT String + ()) Int
  loop i
    | i >= n = get
    | otherwise = do
        step <- ask
        _ <- modify (_ + step)
        current <- get
        _ <- catch (\_ -> pure 0) (if current `mod` 97 == 0 then throw "odd" else pure current)
        loop (i + 1)
