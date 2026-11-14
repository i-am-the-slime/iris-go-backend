module Bench.Harness
  ( benchmark
  , benchmarkEffect
  , benchmarkAff
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (minimum)
import Data.Maybe (fromMaybe)
import Effect (Effect)
import Effect.Aff (Aff, launchAff_)
import Effect.Class (liftEffect)
import Effect.Console (log)
import Effect.Ref as Ref

-- | Runs a pure workload `repetitions` times on an opaque size, prints its result on stdout and
-- | `BENCH best first` (milliseconds) on stderr.
benchmark :: { size :: Int, workload :: Int -> String } -> Effect Unit
benchmark { size, workload } = benchmarkEffect { size, workload: \n -> pure (workload n) }

benchmarkEffect :: { size :: Int, workload :: Int -> Effect String } -> Effect Unit
benchmarkEffect { size, workload } = do
  timings <- Ref.new []
  results <- Ref.new []
  repetitions <- repetitionCount
  startProfile
  forRepetitions repetitions do
    n <- startClock size
    result <- workload n
    elapsed <- stopClock result
    Ref.modify_ (_ `Array.snoc` elapsed) timings
    Ref.modify_ (_ `Array.snoc` result) results
  stopProfile
  report timings results

benchmarkAff :: { size :: Int, workload :: Int -> Aff String } -> Effect Unit
benchmarkAff { size, workload } = launchAff_ do
  timings <- Ref.new [] # liftEffect
  results <- Ref.new [] # liftEffect
  repetitions <- repetitionCount # liftEffect
  startProfile # liftEffect
  forRepetitionsAff repetitions do
    n <- startClock size # liftEffect
    result <- workload n
    elapsed <- stopClock result # liftEffect
    Ref.modify_ (_ `Array.snoc` elapsed) timings # liftEffect
    Ref.modify_ (_ `Array.snoc` result) results # liftEffect
  stopProfile # liftEffect
  report timings results # liftEffect

report :: Ref.Ref (Array Number) -> Ref.Ref (Array String) -> Effect Unit
report timings results = do
  allTimings <- Ref.read timings
  allResults <- Ref.read results
  let first = fromMaybe "" (Array.head allResults)
  log (if Array.all (_ == first) allResults then first else "UNSTABLE " <> show allResults)
  logTiming (fromMaybe 0.0 (minimum allTimings)) (fromMaybe 0.0 (Array.head allTimings))

forRepetitions :: Int -> Effect Unit -> Effect Unit
forRepetitions remaining action = when (remaining > 0) do
  action
  forRepetitions (remaining - 1) action

forRepetitionsAff :: Int -> Aff Unit -> Aff Unit
forRepetitionsAff remaining action = when (remaining > 0) do
  action
  forRepetitionsAff (remaining - 1) action

-- | Records the start time and returns its argument, so that the workload depends on it.
foreign import startClock :: Int -> Effect Int

-- | Milliseconds since `startClock`; takes the result so that it is computed before the clock stops.
foreign import stopClock :: String -> Effect Number

-- | `PATHO_REPETITIONS`, 5 by default.
foreign import repetitionCount :: Effect Int

-- | Starts a CPU profile into `PATHO_CPUPROFILE` when it is set (Go only).
foreign import startProfile :: Effect Unit

foreign import stopProfile :: Effect Unit

foreign import logTiming :: Number -> Number -> Effect Unit
