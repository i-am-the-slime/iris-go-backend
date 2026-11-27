module Main where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)

newtype Trie = Trie { passing :: Int, children :: Map Int Trie }

emptyTrie :: Trie
emptyTrie = Trie { passing: 0, children: Map.empty }

bump :: Trie -> Int -> Trie
bump (Trie node) key = Trie node { children = Map.alter (Just <<< passedThrough) key node.children }
  where
  passedThrough existing = do
    let Trie child = fromMaybe emptyTrie existing
    Trie child { passing = child.passing + 1 }

passingAt :: Int -> Trie -> Int
passingAt key (Trie { children }) = case Map.lookup key children of
  Just (Trie { passing }) -> passing
  Nothing -> 0

main :: Int
main = passingAt 3 trie + passingAt 30 trie
  where
  trie = Array.range 1 1000 <#> (_ `mod` 26) # foldl bump emptyTrie
