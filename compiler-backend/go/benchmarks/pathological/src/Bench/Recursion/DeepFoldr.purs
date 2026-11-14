module Bench.Recursion.DeepFoldr where

import Prelude

import Bench.Harness (benchmark)
import Data.Array ((..))
import Data.Foldable (foldl)
import Data.List (List(..), (:))
import Data.List as List
import Effect (Effect)

hypothesis :: String
hypothesis = "a hand-written non-tail foldr over a 2500-element list recurses 2500 frames deep (deeper overflows V8); Go grows goroutine stacks by copying them"

main :: Effect Unit
main = benchmark { size: 1200, workload }

workload :: Int -> String
workload n = do
  let list = List.fromFoldable (1 .. 2500)
  let total = foldl (\accumulated i -> accumulated + rightFold (\x sum -> (x * i + sum) `mod` 1000003) 0 list) 0 (1 .. n)
  show total

rightFold :: forall a b. (a -> b -> b) -> b -> List a -> b
rightFold combine initial = case _ of
  Nil -> initial
  x : rest -> combine x (rightFold combine initial rest)
