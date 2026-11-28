module Main where

import Prelude

import Control.Alternative (guard)
import Data.Array as Array
import Data.Set (Set)
import Data.Set as Set
import Data.String.CodeUnits (charAt, drop, length, singleton, take)

main :: Int
main = ladderLength "hit" "cog" [ "hot", "dot", "dog", "lot", "log", "cog" ]

ladderLength :: String -> String -> Array String -> Int
ladderLength begin end words = climb 1 [ begin ] (Set.delete begin (Set.fromFoldable words))
  where
  climb :: Int -> Array String -> Set String -> Int
  climb steps level unvisited
    | Array.null level = 0
    | Array.elem end level = steps
    | otherwise = do
        let reached = Set.fromFoldable (Array.filter (_ `Set.member` unvisited) (level >>= oneLetterAway))
        climb (steps + 1) (Set.toUnfoldable reached) (unvisited `Set.difference` reached)

oneLetterAway :: String -> Array String
oneLetterAway word = do
  position <- Array.range 0 (length word - 1)
  letter <- [ 'a', 'c', 'd', 'g', 'h', 'i', 'l', 'o', 't' ]
  guard (charAt position word /= pure letter)
  pure (take position word <> singleton letter <> drop (position + 1) word)
