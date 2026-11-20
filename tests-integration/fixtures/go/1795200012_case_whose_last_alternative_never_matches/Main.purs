module Main where

import Prelude

import Data.Foldable (foldl)
import Data.Int as Int
import Data.List as List
import Data.Maybe (fromMaybe)
import Data.Number as Number

-- Neither number is integral, so each fromNumber is Nothing, a constant the
-- emitter sees only in the Go it has built. The Just alternative of the
-- outer fromMaybe then never matches, and the Nothing alternative before
-- it is the one the case falls to.
defaulted :: Number -> Int
defaulted _ =
  fromMaybe
    ((foldl (\acc _ -> acc) (\x -> x) (List.fromFoldable [ unit, unit, unit ])) (fromMaybe (-17) (Int.fromNumber Number.e)))
    (Int.fromNumber 175.75676)

main :: Array Int
main = [ defaulted 1.0, defaulted 2.0, defaulted 3.0 ]
