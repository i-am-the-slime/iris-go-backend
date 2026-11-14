module Bench.String.SplitJoin where

import Prelude

import Bench.Harness (benchmark)
import Bench.Text as Text
import Data.Array as Array
import Data.String (Pattern(..), joinWith, split, toUpper)
import Data.String.CodeUnits (fromCharArray, toCharArray)
import Effect (Effect)

hypothesis :: String
hypothesis = "split, joinWith, toCharArray and fromCharArray convert between UTF-8 and UTF-16 code units in Go, natively UTF-16 in JS"

main :: Effect Unit
main = benchmark { size: 60000, workload }

workload :: Int -> String
workload n = do
  let asciiRound = roundTrip (Text.ascii n)
  let unicodeRound = roundTrip (Text.unicode n)
  show asciiRound <> " " <> show unicodeRound
  where
  roundTrip text = do
    let words = split (Pattern " ") text
    let shouted = joinWith "," (map toUpper words)
    let characters = toCharArray shouted
    let reversed = fromCharArray (Array.reverse characters)
    Array.length words + Array.length characters + Array.length (split (Pattern ",") reversed)
