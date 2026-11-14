module Bench.Om.ThrowCatch where

import Prelude

import Bench.Harness (benchmarkAff)
import Data.String as String
import Effect (Effect)
import Effect.Aff (Aff)
import Yoga.Om (Om)
import Yoga.Om as Om

hypothesis :: String
hypothesis = "Om.throw injects a Variant ({ type, value } with an erased payload) and handleErrors/onError/mapError match its label against a record of handlers at run time, once per iteration"

main :: Effect Unit
main = benchmarkAff { size: 40000, workload }

type Lookup r = (notFound :: String, invalid :: Int, timeout :: { after :: Int }, conflict :: String | r)

workload :: Int -> Aff String
workload n = loop 0 0 # Om.runOm {} { exception: \_ -> pure "exception", gone: pure }
  where
  loop :: Int -> Int -> Om {} (gone :: String) String
  loop i total
    | i >= n = pure (show total)
    | otherwise = do
        recovered <- attempt i
        loop (i + 1) ((total + recovered) `mod` 1000003)

  attempt :: Int -> Om {} (gone :: String) Int
  attempt i = classify i
    # Om.handleErrors
        { notFound: \message -> pure (String.length message)
        , invalid: \code -> pure (code * 2)
        }
    # Om.onError @"timeout" (\{ after } -> pure (after + 1))
    # Om.mapError @"conflict" @"gone" (_ <> "!")
    # Om.handleErrors { gone: \message -> pure (String.length message + 100) }

  classify :: forall r. Int -> Om {} (Lookup r) Int
  classify i = case i `mod` 6 of
    0 -> Om.throw { notFound: "item " <> show i }
    1 -> Om.throw { invalid: i `mod` 97 }
    2 -> Om.throw { timeout: { after: i `mod` 17 } }
    3 -> Om.throw { conflict: "version" }
    4 -> do
      Om.throwWhen { invalid: 1 } (i `mod` 4 == 0)
      pure i
    _ -> pure (i `mod` 13)
