module Bench.Persistent.ObjectChurn where

import Prelude

import Bench.Harness (benchmark)
import Data.Array ((..))
import Data.Foldable (foldl)
import Data.Maybe (fromMaybe)
import Effect (Effect)
import Foreign.Object as Object

hypothesis :: String
hypothesis = "Foreign.Object insert and delete copy the whole object; JS copies a dictionary-mode object, Go copies a hash map"

main :: Effect Unit
main = benchmark { size: 20000, workload }

workload :: Int -> String
workload n = do
  let final = foldl churn Object.empty (1 .. n)
  show (Object.size final) <> " " <> show (Object.lookup "k42" final) <> " " <> show (foldl (+) 0 final)
  where
  churn object i = do
    let key = "k" <> show ((i * 31) `mod` 300)
    let inserted = Object.insert key i object
    let deleted = Object.delete ("k" <> show ((i * 17) `mod` 300)) inserted
    Object.insert key (fromMaybe 0 (Object.lookup key deleted) + 1) deleted
