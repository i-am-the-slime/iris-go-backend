module Bench.Generic.ShowEqOrd where

import Prelude

import Bench.Harness (benchmark)
import Data.Array ((..))
import Data.Array as Array
import Data.Generic.Rep (class Generic)
import Data.Eq.Generic (genericEq)
import Data.Ord.Generic (genericCompare)
import Data.Show.Generic (genericShow)
import Data.String.CodeUnits as CodeUnits
import Effect (Effect)

hypothesis :: String
hypothesis = "genericShow, genericEq and genericCompare go through Generic.Rep sums and products: many tiny allocations per constructor"

data Point = Point Int Int

derive instance Generic Point _
instance Show Point where
  show = genericShow
instance Eq Point where
  eq = genericEq
instance Ord Point where
  compare = genericCompare

data Shape
  = Circle Point Number
  | Rectangle { corner :: Point, width :: Int, height :: Int }
  | Polygon (Array Point)
  | Group String (Array Shape)

derive instance Generic Shape _
instance Show Shape where
  show shape = genericShow shape
instance Eq Shape where
  eq left right = genericEq left right
instance Ord Shape where
  compare left right = genericCompare left right

main :: Effect Unit
main = benchmark { size: 6000, workload }

workload :: Int -> String
workload n = do
  let shapes = map shape (1 .. n)
  let copies = map shape (1 .. n)
  let shown = CodeUnits.length (show shapes)
  let equal = Array.length (Array.filter identity (Array.zipWith eq shapes copies))
  let sorted = Array.sort shapes
  show shown <> " " <> show equal <> " " <> CodeUnits.take 60 (show (Array.head sorted))
  where
  shape i = case i `mod` 4 of
    0 -> Circle (Point i (i * 2)) (toFraction i)
    1 -> Rectangle { corner: Point (i `mod` 17) i, width: i `mod` 9, height: 3 }
    2 -> Polygon (map (\j -> Point j (i - j)) (0 .. (i `mod` 6)))
    _ -> Group ("g" <> show (i `mod` 23)) [ Circle (Point 1 i) 0.5, Polygon [ Point i i ] ]

  toFraction i = if i `mod` 2 == 0 then 1.25 else 0.1
