module Main where

import Prelude

import Data.Foldable (foldl)
import Data.Map as Map
import Data.Set as Set
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)

foreign import log :: String -> Effect Unit

foreign import timed :: forall a. (Unit -> a) -> Effect a

main :: Effect Unit
main = do
  ints <- timed \_ -> foldl (\built key -> Map.insert key key built) Map.empty keys
  log (show (Map.toUnfoldable ints :: Array (Int /\ Int)))
  pairs <- timed \_ -> foldl (\built key -> Map.insert (key `mod` 3 /\ key / 3) key built) Map.empty keys
  log (show (Map.toUnfoldable pairs :: Array ((Int /\ Int) /\ Int)))
  words <- timed \_ -> foldl (\built word -> Map.insert word 1 built) Map.empty names
  log (show (Map.toUnfoldable words :: Array (String /\ Int)))
  intSet <- timed \_ -> foldl (flip Set.insert) Set.empty keys
  log (show (Set.toUnfoldable intSet :: Array Int))
  wordSet <- timed \_ -> foldl (flip Set.insert) Set.empty names
  log (show (Set.toUnfoldable wordSet :: Array String))
  where
  keys = [ 17, 3, 11, 3, 29, 0, 8, 17, 22, 5, 14 ]
  names = [ "pear", "apple", "fig", "apple", "kiwi", "banana", "fig" ]
