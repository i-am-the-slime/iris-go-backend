module Bench.Fallback.UnsafeCoerce where

import Prelude

import Bench.Harness (benchmark)
import Data.Array ((..))
import Data.Foldable (foldl)
import Data.String.CodeUnits as CodeUnits
import Effect (Effect)
import Foreign (Foreign)
import Unsafe.Coerce (unsafeCoerce)

hypothesis :: String
hypothesis = "a dynamically tagged heap built with unsafeCoerce: JS just passes the value, Go must box it and assert its real type back"

type Dynamic = Foreign

data Tag = IntTag | StringTag | ArrayTag

type Cell = { tag :: Tag, payload :: Dynamic }

main :: Effect Unit
main = benchmark { size: 400000, workload }

workload :: Int -> String
workload n = do
  let cells = map cell (1 .. n)
  show (foldl (\total c -> total + measure c) 0 cells)
  where
  cell i = case i `mod` 3 of
    0 -> { tag: IntTag, payload: toDynamic i }
    1 -> { tag: StringTag, payload: toDynamic (show i) }
    _ -> { tag: ArrayTag, payload: toDynamic [ i, i + 1 ] }

  measure { tag, payload } = case tag of
    IntTag -> (fromDynamic payload :: Int) `mod` 7
    StringTag -> CodeUnits.length (fromDynamic payload)
    ArrayTag -> foldl (+) 0 (fromDynamic payload :: Array Int) `mod` 5

toDynamic :: forall a. a -> Dynamic
toDynamic = unsafeCoerce

fromDynamic :: forall a. Dynamic -> a
fromDynamic = unsafeCoerce
