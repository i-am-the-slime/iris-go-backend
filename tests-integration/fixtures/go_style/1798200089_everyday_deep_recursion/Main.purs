module Fun.Deep where

import Prelude

import Data.Array ((..))
import Data.Array as Array
import Data.Foldable (foldr, foldl, sum)
import Data.List (List(..), (:))
import Data.List as List
import Data.List.Lazy as LazyList
import Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Console (log)

sumTo :: Int -> Int
sumTo 0 = 0
sumTo n = n + sumTo (n - 1)

buildList :: Int -> List Int
buildList 0 = Nil
buildList n = n : buildList (n - 1)

countNodes :: List Int -> Int
countNodes = case _ of
  Nil -> 0
  _ : rest -> 1 + countNodes rest

main :: Effect Unit
main = do
  log $ show (sumTo 5000)
  log $ show (countNodes (buildList 5000))
  log $ show (foldr (+) 0 (1 .. 1000000))
  log $ show (List.length (List.range 1 1000000))
  log $ show (foldr (\n acc -> acc + n) 0 (List.range 1 1000000))
  log $ show (List.foldl (+) 0 (List.range 1 1000000))
  log $ show (sum (List.range 1 1000000 # map (_ * 2) # List.filter (_ > 5)))
  log $ show (LazyList.foldl (+) 0 (LazyList.take 1000000 (LazyList.iterate (_ + 1) 0)))
  log $ show (List.reverse (List.range 1 10))
  log $ show (Array.fromFoldable (List.range 1 5) <> Array.reverse (1 .. 3))
  let bigMap = foldl (\m i -> Map.insert i (i * i) m) Map.empty (1 .. 100000)
  log $ show (Map.size bigMap) <> " " <> show (fromMaybe 0 (Map.lookup 777 bigMap))
  log $ show (foldr (\(k /\ v) acc -> acc + k + v `mod` 7) 0 (Map.toUnfoldable bigMap :: Array _))
  log $ show (Array.length (Array.concatMap (\i -> [ i, i ]) (1 .. 500000)))
  log $ show (List.toUnfoldable (List.sort (List.fromFoldable [ 5, 3, 9, 1 ])) :: Array Int)
