module Main where

import Prelude

import Data.Foldable (foldl)
import Data.HashMap (HashMap)
import Data.HashMap as HashMap
import Data.Hashable (class Hashable)
import Data.Maybe (fromMaybe)
import Data.Tuple.Nested (type (/\), (/\))
import Foreign.Object (Object)
import Foreign.Object as Object

type Tally = { byWord :: HashMap String Int, byFirst :: Object Int, lengths :: HashMap Int Int }

tally :: Array String -> Tally
tally = foldl step { byWord: HashMap.empty, byFirst: Object.empty, lengths: HashMap.empty }
  where
  step counts word = do
    let seen = fromMaybe 0 (HashMap.lookup word counts.byWord)
    { byWord: HashMap.insert word (seen + 1) counts.byWord
    , byFirst: Object.insert word (seen + 1) counts.byFirst
    , lengths: HashMap.insertWith (+) (if word == "" then 0 else 1) 1 counts.lengths
    }

newtype Point = Point { x :: Int, y :: Int }

derive newtype instance Eq Point
derive newtype instance Hashable Point

points :: Array Int -> HashMap Point Int
points = foldl (\seen n -> HashMap.insert (Point { x: n, y: -n }) n (HashMap.delete (Point { x: n - 1, y: 1 - n }) seen)) HashMap.empty

keptVersion :: Array Int -> Int /\ Int
keptVersion numbers = do
  let table /\ before = foldl step (HashMap.empty /\ 0) numbers
  HashMap.size table /\ before
  where
  step (table /\ _) n = HashMap.insert n n table /\ HashMap.size table

main :: Array String
main = do
  let counts = tally [ "a", "b", "a", "" ]
  [ show (HashMap.toArrayBy (/\) counts.byWord)
  , show (Object.size counts.byFirst)
  , show (HashMap.lookup 1 counts.lengths)
  , show (HashMap.size (points [ 1, 2, 3, 4 ]))
  , show (keptVersion [ 1, 2, 3 ])
  ]
