module Bench.Persistent.ArrayNonOwned where

import Prelude

import Bench.Harness (benchmark)
import Data.Array ((..))
import Data.Array as Array
import Data.Foldable (foldl, sum)
import Data.Maybe (Maybe(..), fromMaybe)
import Effect (Effect)

hypothesis :: String
hypothesis = "updateAt, insertAt, cons, snoc, unsnoc and uncons on arrays that stay alive must copy; JS copies with a memcpy-like builtin, Go allocates and copies too"

main :: Effect Unit
main = benchmark { size: 3000, workload }

workload :: Int -> String
workload n = do
  let base = 1 .. 2000
  let total = foldl (\accumulated i -> accumulated + touch base i) 0 (1 .. n)
  let drained = drain (Array.take 3000 (1 .. n)) 0
  show total <> " " <> show drained <> " " <> show (sum base)
  where
  touch base i = do
    let updated = fromMaybe base (Array.updateAt (i `mod` 2000) i base)
    let inserted = fromMaybe base (Array.insertAt (i `mod` 2001) i base)
    let consed = Array.cons i base
    let snoced = Array.snoc base i
    let unsnoced = maybe0 (map _.last (Array.unsnoc snoced))
    let unconsed = maybe0 (map _.head (Array.uncons consed))
    Array.length updated + Array.length inserted + unsnoced + unconsed + fromMaybe 0 (Array.index inserted 7)

  drain array count = case Array.uncons array of
    Just { head, tail } -> drain tail (count + head)
    Nothing -> count

  maybe0 = fromMaybe 0
