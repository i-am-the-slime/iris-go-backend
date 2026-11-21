module Main where

import Prelude

import Data.Array (length, snoc, (..))
import Data.String (Pattern(..), contains, split)

-- | `show` of an Int and of a Boolean is Go's `strconv`, and the Boolean is tested in place.
describe :: Int -> String
describe count = do
  let many = count > 1
  "count " <> show count <> ", many " <> show many

-- | `contains` and `split` on a constant are Go's `strings`.
words :: String -> Array String
words text = if contains (Pattern "-") text then split (Pattern "-") text else [ text ]

-- | A local keeps a package's name, and the package is imported under another.
lengths :: Int -> String
lengths n = do
  let strconv = snoc (1 .. n) 9
  show (length strconv) <> show strconv

-- | A `let` of an `if` keeps its name.
price :: Int -> Number
price quantity = do
  let discount = if quantity >= 10 then 0.15 else 0.0
  1.0 - discount

main :: Array String
main = do
  let counts = 1 .. 3
  map describe counts
    <> words (show counts)
    <> map lengths counts
    <> map (\count -> show (price count)) counts
