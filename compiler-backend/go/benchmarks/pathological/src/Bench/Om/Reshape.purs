module Bench.Om.Reshape where

import Prelude

import Bench.Harness (benchmarkAff)
import Control.Monad.Error.Class (catchError)
import Data.Either (Either(..))
import Data.String as String
import Data.Variant as Variant
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Type.Proxy (Proxy(..))
import Yoga.Om (Om, ask, asks)
import Yoga.Om as Om

hypothesis :: String
hypothesis = "expand/expandCtx/widenCtx reshape the context record (Record.Studio shrink, disjointUnion) and sequenceOmRecord folds a heterogeneous record of Oms: each step rebuilds a record that JS shares, and coerces a rank-N RWSET between error rows"

main :: Effect Unit
main = benchmarkAff { size: 15000, workload }

type Small = { base :: Int }

type Large = { base :: Int, scale :: Int, name :: String }

workload :: Int -> Aff String
workload n = do
  counter <- Ref.new 0 # liftEffect
  loop counter 0 0 # Om.runOm { base: 5, scale: 3, name: "reshape" } { exception: \_ -> pure "exception", parse: pure }
  where
  loop :: Ref.Ref Int -> Int -> Int -> Om Large (parse :: String) String
  loop counter i total
    | i >= n = do
        name <- asks _.name
        seen <- Ref.read counter # liftEffect
        pure (name <> " " <> show total <> " " <> show seen)
    | otherwise = do
        fields <- Om.sequenceOmRecord
          { small: smallStep i
          , parsed: parsed i
          , recovered: recovered (i + 1)
          , widened: widened i # Om.widenCtx { offset: i `mod` 11 }
          }
        again <- Om.expand (smallStep (i + 2))
        tapped <- pure (fields.small + again) # Om.tapM \value -> Ref.modify_ (_ + value `mod` 3) counter # liftEffect
        loop counter (i + 1) ((total + tapped + fields.parsed + fields.recovered + fields.widened) `mod` 1000003)

  smallStep :: Int -> Om Small () Int
  smallStep i = checked # Om.handleErrors { odd: \odd -> pure (odd `mod` 5) }
    where
    checked = do
      { base } <- ask
      Om.throwWhen { odd: i } (i `mod` 9 == 4)
      pure (base + i `mod` 7)

  -- catchError keeps the error row and re-dispatches the label with Variant.on/default.
  recovered :: Int -> Om Large (parse :: String) Int
  recovered i = catchError (digits i # Om.mapError @"invalidDigits" @"parse" identity)
    (Variant.default (Om.fatal "unexpected") # Variant.on (Proxy :: Proxy "parse") (\message -> pure (String.length message * 2)))

  parsed :: Int -> Om Large (parse :: String) Int
  parsed i = Om.mapError @"invalidDigits" @"parse" (_ <> " (mapped)") (digits i)
    # Om.onError @"parse" (\message -> pure (String.length message))

  digits :: forall r. Int -> Om Large (invalidDigits :: String | r) Int
  digits i = toDigits (show i) # Om.throwLeftAs (\invalidDigits -> Om.error { invalidDigits })
    where
    toDigits text
      | String.length text `mod` 2 == 0 = Right (String.length text)
      | otherwise = Left text

  widened :: Int -> Om { offset :: Int, base :: Int, scale :: Int, name :: String } (parse :: String) Int
  widened i = do
    { offset, scale } <- ask
    pure ((offset + i) * scale `mod` 101)
