module Bench.Record.PassBig where

import Prelude

import Bench.Harness (benchmark)
import Data.Array as Array
import Effect (Effect)

hypothesis :: String
hypothesis = "a 20-field record with strings and arrays is a large Go struct copied by value at every call and return; JS passes one pointer"

type Big =
  { name :: String, title :: String, tags :: Array String, scores :: Array Int
  , x :: Number, y :: Number, width :: Number, height :: Number
  , red :: Int, green :: Int, blue :: Int, alpha :: Int
  , visible :: Boolean, selected :: Boolean, locked :: Boolean
  , depth :: Int, parent :: String, kind :: String, version :: Int, checksum :: Int
  }

main :: Effect Unit
main = benchmark { size: 1000000, workload }

workload :: Int -> String
workload n = do
  let final = loop 0 initial
  show final.version <> " " <> show final.checksum <> " " <> show final.x <> " " <> final.name
  where
  loop i big
    | i >= n = big
    | otherwise = loop (i + 1) (step i (normalise big))

step :: Int -> Big -> Big
step i big
  | i `mod` 2 == 0 = moveBy 1.5 big
  | otherwise = recolour i (bump big)

moveBy :: Number -> Big -> Big
moveBy distance big = big { x = big.x + distance, y = big.y - distance }

recolour :: Int -> Big -> Big
recolour i big = big { red = (big.red + i) `mod` 256, alpha = Array.length big.tags + big.alpha `mod` 7 }

bump :: Big -> Big
bump big = big { version = big.version + 1, checksum = (big.checksum * 31 + big.version) `mod` 1000003 }

normalise :: Big -> Big
normalise big
  | big.x > 1000.0 = big { x = 0.0, selected = not big.selected }
  | otherwise = big

initial :: Big
initial =
  { name: "node", title: "Node", tags: [ "a", "b" ], scores: [ 1, 2, 3 ]
  , x: 0.0, y: 0.0, width: 10.0, height: 20.0
  , red: 1, green: 2, blue: 3, alpha: 4
  , visible: true, selected: false, locked: false
  , depth: 0, parent: "root", kind: "box", version: 0, checksum: 7
  }
