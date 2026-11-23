module Main where

import Prelude

import Data.Array as Array
import Data.Foldable (all, and, any, elem, foldl, notElem, or)
import Data.FoldableWithIndex (allWithIndex, anyWithIndex)
import Partial.Unsafe (unsafeCrashWith)

positiveUnlessCrashing :: Int -> Boolean
positiveUnlessCrashing x
  | x == 0 = unsafeCrashWith "evaluated past the deciding element"
  | otherwise = x > 0

negativeUnlessCrashing :: Int -> Boolean
negativeUnlessCrashing x
  | x == 0 = unsafeCrashWith "evaluated past the deciding element"
  | otherwise = x < 0

safeFrom :: Array Int -> Int -> Boolean
safeFrom placed queen = allWithIndex notAttacking placed
  where
  notAttacking i other = other /= queen && distance other /= i + 1
  distance other = if other > queen then other - queen else queen - other

main :: Array Boolean
main =
  [ Array.all positiveUnlessCrashing [ 1, -2, 0 ]
  , Array.any negativeUnlessCrashing [ 1, -2, 0 ]
  , all (_ > 0) [ 1, 2, -3, 4 ]
  , any (_ < 0) [ 1, 2, -3, 4 ]
  , all (_ > 0) ([] :: Array Int)
  , any (_ < 0) ([] :: Array Int)
  , allWithIndex (\i x -> x > i) [ 1, 2, 3, 2 ]
  , anyWithIndex (\i x -> x == i) [ 1, 2, 2, 4 ]
  , and [ true, false, true ]
  , or [ false, true, false ]
  , elem 3 [ 1, 2, 3, 4 ]
  , notElem 5 [ 1, 2, 3, 4 ]
  , foldl (\accumulated x -> accumulated && x > 0) true [ 1, -2, 3 ]
  , foldl (\accumulated x -> x < 0 || accumulated) false [ 1, -2, 3 ]
  , Array.foldr (\x accumulated -> if x > 2 then accumulated else false) true [ 3, 4, 1 ]
  , safeFrom [ 2, 4, 1 ] 3
  , safeFrom [ 2, 4, 1 ] 5
  ]
