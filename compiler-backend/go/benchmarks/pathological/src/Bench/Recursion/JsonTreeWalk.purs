module Bench.Recursion.JsonTreeWalk where

import Prelude

import Bench.Harness (benchmark)
import Data.Array ((..))
import Data.Foldable (foldl, maximum, sum)
import Data.Maybe (fromMaybe)
import Data.String.CodeUnits as CodeUnits
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)

hypothesis :: String
hypothesis = "a JSON-like tree of arrays and key/value pairs walked by non-tail recursion; small allocations and indirect recursion"

data Json
  = JNull
  | JBool Boolean
  | JNumber Number
  | JString String
  | JArray (Array Json)
  | JObject (Array (String /\ Json))

main :: Effect Unit
main = benchmark { size: 9, workload }

workload :: Int -> String
workload depth = do
  let document = generate depth 0
  show (nodes document) <> " " <> show (height document) <> " " <> show (characters document) <> " " <> show (numbers document)
  where
  generate 0 seed = leaf seed
  generate d seed = case seed `mod` 3 of
    0 -> JArray (map (\i -> generate (d - 1) (seed * 4 + i)) (0 .. 3))
    1 -> JObject (map (\i -> ("key" <> show i) /\ generate (d - 1) (seed * 5 + i)) (0 .. 4))
    _ -> JArray [ leaf seed, generate (d - 1) (seed + 1), generate (d - 1) (seed + 2) ]

  leaf seed = case seed `mod` 4 of
    0 -> JNull
    1 -> JBool (seed `mod` 8 == 1)
    2 -> JNumber (0.5 * toNumberish seed)
    _ -> JString ("s" <> show seed)

  toNumberish seed = foldl (\total _ -> total + 1.0) 0.0 (0 .. (seed `mod` 3))

  nodes = case _ of
    JArray items -> 1 + sum (map nodes items)
    JObject fields -> 1 + sum (map (\(_ /\ v) -> nodes v) fields)
    _ -> 1

  height = case _ of
    JArray items -> 1 + fromMaybe 0 (maximum (map height items))
    JObject fields -> 1 + fromMaybe 0 (maximum (map (\(_ /\ v) -> height v) fields))
    _ -> 0

  characters = case _ of
    JString text -> CodeUnits.length text
    JArray items -> sum (map characters items)
    JObject fields -> sum (map (\(k /\ v) -> CodeUnits.length k + characters v) fields)
    _ -> 0

  numbers = case _ of
    JNumber number -> number
    JArray items -> sum (map numbers items)
    JObject fields -> sum (map (\(_ /\ v) -> numbers v) fields)
    _ -> 0.0
