module Bench.Idiom.Data.BTreeCheck where

import Prelude

import Data.Array ((..))
import Data.Array as Array
import Data.BTreeMap as BTree
import Data.Foldable (foldl, foldr)
import Data.FoldableWithIndex (foldlWithIndex, foldrWithIndex)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Console (log)

-- | Seeded random operation sequences on Data.Map and Data.BTreeMap side by side; every few
-- | steps both must show, fold and list the same.
main :: Effect Unit
main = (1 .. 6) <#> runSeed # Array.intercalate "\n" # log

runSeed :: Int -> String
runSeed seed = do
  let final = foldl step { random: seed, ordered: Map.empty, tree: BTree.empty, report: [] } (1 .. steps)
  "seed " <> show seed <> ": " <> Array.intercalate " " final.report <> "\n" <> show final.tree
  where
  steps = 1500 + seed * 700
  keyRange = 50 + seed * 120
  step state index = do
    let r1 = next state.random
    let r2 = next r1
    let key = r1 `mod` keyRange
    let value = r2 `mod` 1000
    let ordered /\ tree = operation (r2 `mod` 7) key value state.ordered state.tree
    let report = if index `mod` 250 == 0 then Array.snoc state.report (compareBoth ordered tree) else state.report
    { random: r2, ordered, tree, report }
  operation choice key value ordered tree = case choice of
    0 -> Map.insert key value ordered /\ BTree.insert key value tree
    1 -> Map.insertWith (\old new -> old * 3 + new) key value ordered /\ BTree.insertWith (\old new -> old * 3 + new) key value tree
    2 -> Map.delete key ordered /\ BTree.delete key tree
    3 -> Map.alter (alterBy value) key ordered /\ BTree.alter (alterBy value) key tree
    4 -> Map.update (updateBy value) key ordered /\ BTree.update (updateBy value) key tree
    5 -> do
      let pairs = (0 .. (value `mod` 40)) <#> \i -> (key + i * 3) /\ (value + i)
      Map.unionWith (+) ordered (Map.fromFoldable pairs) /\ BTree.unionWith (+) tree (BTree.fromFoldable pairs)
    _ -> Map.insert key value ordered /\ BTree.insert (key + 0) value tree
  alterBy value = case _ of
    Nothing -> Just value
    Just old | old `mod` 3 == 0 -> Nothing
    Just old -> Just (old + value)
  updateBy value old = if (old + value) `mod` 4 == 0 then Nothing else Just (old - value)

compareBoth :: Map.Map Int Int -> BTree.Map Int Int -> String
compareBoth ordered tree = verdict
  where
  verdict
    | sameEntries && sameFolds && sameLookups = show (Map.size ordered) <> ":" <> show (foldl (+) 0 ordered)
    | otherwise = "MISMATCH " <> show ordered <> " vs " <> show tree
  sameEntries = show ordered == show tree && (Map.toUnfoldable ordered :: Array (Tuple Int Int)) == BTree.toArray tree
    && Array.fromFoldable (Map.values ordered) == BTree.values tree
  sameFolds = foldr (\v acc -> acc * 7 + v) 0 ordered == foldr (\v acc -> acc * 7 + v) 0 tree
    && foldlWithIndex (\k acc v -> acc * 5 + k - v) 0 ordered == foldlWithIndex (\k acc v -> acc * 5 + k - v) 0 tree
    && foldrWithIndex (\k v acc -> acc * 3 + k * v) 0 ordered == foldrWithIndex (\k v acc -> acc * 3 + k * v) 0 tree
  sameLookups = Array.all (\k -> Map.lookup k ordered == BTree.lookup k tree) (-1 .. 400)

next :: Int -> Int
next x = (x * 75 + 74) `mod` 65537
