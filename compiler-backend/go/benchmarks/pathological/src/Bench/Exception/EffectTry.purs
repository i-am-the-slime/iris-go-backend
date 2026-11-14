module Bench.Exception.EffectTry where

import Prelude

import Bench.Harness (benchmarkEffect)
import Data.Either (Either(..))
import Effect (Effect, forE)
import Effect.Exception (catchException, error, message, throwException, try)
import Effect.Ref as Ref

hypothesis :: String
hypothesis = "throwException caught by try or catchException in a hot loop; Go implements it with panic and recover, which unwind slowly"

main :: Effect Unit
main = benchmarkEffect { size: 200000, workload }

workload :: Int -> Effect String
workload n = do
  caught <- Ref.new 0
  lengths <- Ref.new 0
  forE 0 n (step caught lengths)
  total <- Ref.read caught
  characters <- Ref.read lengths
  pure (show total <> " " <> show characters)
  where
  step caught lengths i = do
    outcome <- try (risky i)
    case outcome of
      Left problem -> Ref.modify_ (_ + 1) caught *> Ref.modify_ (_ + messageLength problem) lengths
      Right value -> Ref.modify_ (_ + value `mod` 2) lengths
    recovered <- catchException (\_ -> pure 1) (risky (i + 1))
    Ref.modify_ (_ + recovered `mod` 3) lengths

  risky i
    | i `mod` 3 == 0 = throwException (error ("failure " <> show i))
    | otherwise = pure i

  messageLength problem = if message problem == "" then 0 else 1
