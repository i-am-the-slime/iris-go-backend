module Main where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NonEmptyArray
import Data.Ord (comparing)
import Effect (Effect)
import Effect.Ref as Ref

main :: Effect Unit
main = do
  shown <- Ref.new ""
  let record text = Ref.modify_ (_ <> text) shown
  record (show (Array.nub [ 3, 1, 3, 2, 1 ]))
  record (show (Array.nub [ "b", "a", "b" ]))
  record (show (Array.nub [ 'x', 'y', 'x' ]))
  record (show (Array.nub [ true, false, true ]))
  record (show (Array.nub [ 1.5, 0.5, 1.5 ]))
  record (show (Array.nubBy (comparing (_ `mod` 3)) [ 1, 4, 2, 5, 3 ]))
  record (show (map NonEmptyArray.toArray (Array.group [ 1, 1, 2, 3, 3 ])))
  record (show (map NonEmptyArray.toArray (Array.groupBy (\first x -> x - first < 2) [ 1, 2, 3, 4, 7 ])))
