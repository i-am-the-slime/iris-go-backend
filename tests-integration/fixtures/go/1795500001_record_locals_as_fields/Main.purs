module Main where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.FoldableWithIndex (foldlWithIndex)

type Body = { x :: Number, y :: Number, vx :: Number, vy :: Number, mass :: Number }

-- | The accumulator lives as one local per field it reads or writes; the mass it never reads
-- | has no local, and the step's position update writes into the accumulator's own locals.
-- | Their values go into the array element field by field, as a struct of five fields would be
-- | built on the stack and copied.
advance :: Array Body -> Array Body
advance bodies = map move (Array.mapWithIndex accelerate bodies)
  where
  accelerate i body = foldlWithIndex (pull i) body bodies

  pull i j acc other
    | i == j = acc
    | otherwise = acc { vx = acc.vx + (other.x - acc.x) * other.mass, vy = acc.vy + (other.y - acc.y) * other.mass }

  move body = body { x = body.x + body.vx, y = body.y + body.vy }

type Tally = { count :: Int, total :: Int, label :: String, seen :: Boolean }

-- | Fields that start as literals keep their record's types: an Int field is an int32 local.
-- | Where the result is used whole, it is built from every field's local.
tally :: Array Int -> Tally
tally = foldl step { count: 0, total: 0, label: "", seen: false }
  where
  step acc n = acc { count = acc.count + 1, total = acc.total + n, label = acc.label <> show n, seen = acc.seen || n > 2 }

-- | Nested folds over records: each accumulator's field locals are its own.
grid :: Array Int -> { rows :: Int, cells :: Int }
grid rows = foldl row { rows: 0, cells: 0 } rows
  where
  row acc width = do
    let inner = foldl (\cells _ -> cells { cells = cells.cells + 1, rows = cells.rows }) { rows: 0, cells: acc.cells } (Array.range 1 width)
    acc { rows = acc.rows + 1, cells = inner.cells }

type Pair = { left :: Int, right :: Int }

-- | Fields swapped by one update read the values from before the update.
swaps :: Int -> Pair
swaps n = foldl (\acc i -> acc { left = acc.right + i, right = acc.left }) { left: 1, right: 2 } (Array.range 1 n)

main :: Array String
main =
  [ show (advance [ { x: 0.0, y: 0.0, vx: 0.0, vy: 0.0, mass: 1.0 }, { x: 1.0, y: 2.0, vx: 0.5, vy: 0.0, mass: 0.5 }, { x: -1.0, y: 0.5, vx: 0.0, vy: 0.25, mass: 2.0 } ])
  , show (tally [ 1, 2, 3, 4 ])
  , show (Array.reverse [ tally [ 5 ], tally [ 1, 2, 3 ] ])
  , show (grid [ 2, 3, 4 ])
  , show (swaps 5)
  ]
