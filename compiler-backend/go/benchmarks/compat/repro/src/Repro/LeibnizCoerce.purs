module Repro.LeibnizCoerce where

import Prelude

import Data.Leibniz (type (~), coerce, symm)
import Effect (Effect)
import Effect.Console (log)

data Value a = IntValue (a ~ Int) Int | StringValue (a ~ String) String

evaluate :: forall a. Value a -> a
evaluate (IntValue proof n) = coerce (symm proof) n
evaluate (StringValue proof s) = coerce (symm proof) s

main :: Effect Unit
main = log (show (evaluate (IntValue identity 41) + 1))
