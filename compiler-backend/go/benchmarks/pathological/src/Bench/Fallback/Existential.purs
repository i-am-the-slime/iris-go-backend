module Bench.Fallback.Existential where

import Prelude

import Bench.Harness (benchmark)
import Data.Array ((..))
import Data.Exists (Exists, mkExists, runExists)
import Data.Foldable (foldl)
import Data.String.CodeUnits as CodeUnits
import Effect (Effect)

hypothesis :: String
hypothesis = "Data.Exists hides a type behind unsafeCoerce; Go must erase the hidden type to any and assert on every use"

data Described a = Described a (a -> String) (a -> a)

type Anything = Exists Described

main :: Effect Unit
main = benchmark { size: 200000, workload }

workload :: Int -> String
workload n = do
  let boxes = map box (1 .. n)
  let stepped = map (runExists \(Described value describe next) -> mkExists (Described (next value) describe next)) boxes
  show (foldl (\total thing -> total + runExists (\(Described value describe _) -> CodeUnits.length (describe value)) thing) 0 stepped)
  where
  box i = case i `mod` 3 of
    0 -> mkExists (Described i show (_ + 1))
    1 -> mkExists (Described (show i) identity (_ <> "!"))
    _ -> mkExists (Described [ i, i ] show (map (_ * 2)))
