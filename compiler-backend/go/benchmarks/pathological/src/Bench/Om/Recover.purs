module Bench.Om.Recover where

import Prelude

import Bench.Harness (benchmarkAff)
import Control.Monad.Error.Class (catchError)
import Data.Either (Either(..))
import Data.Map as Map
import Data.String as String
import Data.Tuple.Nested ((/\))
import Data.Variant as Variant
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Type.Proxy (Proxy(..))
import Yoga.Om (Om, ask, asks)
import Yoga.Om as Om

hypothesis :: String
hypothesis = "the README's helpers (note, throwLeftAs, mapError, onError, tapM, catchError with Variant.on/default) each wrap the computation in another RWSET layer and re-inject or re-match a Variant, so one recovered value costs several CPS layers and label compares"

main :: Effect Unit
main = benchmarkAff { size: 20000, workload }

type Context = { names :: Map.Map Int String, seen :: Ref Int }

workload :: Int -> Aff String
workload n = do
  seen <- Ref.new 0 # liftEffect
  loop 0 0 # Om.runOm { names, seen } { exception: \_ -> pure "exception", parse: pure }
  where
  names = Map.fromFoldable (map (\i -> i /\ ("name" <> show i)) [ 0, 2, 3, 5, 7, 11, 13 ])

  loop :: Int -> Int -> Om Context (parse :: String) String
  loop i total
    | i >= n = do
        count <- asks _.seen >>= (Ref.read >>> liftEffect)
        pure (show total <> " " <> show count)
    | otherwise = do
        named <- lookupName i
        parsed <- parseDigits i
        recovered <- recoverParse (i + 1)
        loop (i + 1) ((total + named + parsed + recovered) `mod` 1000003)

  lookupName :: Int -> Om Context (parse :: String) Int
  lookupName i = found # Om.handleErrors { missing: \key -> pure key }
    where
    found = do
      { names: table } <- ask
      name <- Map.lookup (i `mod` 17) table # Om.note { missing: i `mod` 5 }
      pure (String.length name)
        # Om.tapM \length -> countSeen length

  parseDigits :: Int -> Om Context (parse :: String) Int
  parseDigits i = Om.mapError @"invalidDigits" @"parse" (_ <> " (mapped)") (digits i)
    # Om.onError @"parse" (\message -> pure (String.length message))

  recoverParse :: Int -> Om Context (parse :: String) Int
  recoverParse i = catchError (digits i # Om.mapError @"invalidDigits" @"parse" identity)
    (Variant.default (Om.fatal "unexpected") # Variant.on (Proxy :: Proxy "parse") (\message -> pure (String.length message * 2)))

  digits :: forall r. Int -> Om Context (invalidDigits :: String | r) Int
  digits i = toDigits (show i) # Om.throwLeftAs (\invalidDigits -> Om.error { invalidDigits })
    where
    toDigits text
      | String.length text `mod` 2 == 0 = Right (String.length text)
      | otherwise = Left text

  countSeen :: forall r. Int -> Om Context r Unit
  countSeen length = do
    seen <- asks _.seen
    Ref.modify_ (_ + length `mod` 3) seen # liftEffect
