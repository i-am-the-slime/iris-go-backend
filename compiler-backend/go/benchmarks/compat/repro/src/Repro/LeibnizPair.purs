module Repro.LeibnizPair where

import Prelude

import Data.Leibniz (type (~), coerce, symm)
import Effect (Effect)
import Effect.Console (log)

data Value a
  = IntValue (a ~ Int) Int
  | StringValue (a ~ String) String
  | Pair (Value a) (Value a)

evaluate :: forall a. Value a -> a
evaluate (IntValue proof n) = coerce (symm proof) n
evaluate (StringValue proof s) = coerce (symm proof) s
evaluate (Pair a _) = evaluate a

main :: Effect Unit
main = do
  log (show (evaluate (IntValue identity 41) + 1))
  log (evaluate (Pair (StringValue identity "left") (StringValue identity "right")))
