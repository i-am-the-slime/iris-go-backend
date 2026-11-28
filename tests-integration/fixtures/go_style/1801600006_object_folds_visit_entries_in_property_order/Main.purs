module Main where

import Prelude

import Data.Array as Array
import Data.Foldable (all, any, foldMap, foldl, foldr, for_, sum)
import Data.FoldableWithIndex (foldlWithIndex, foldrWithIndex)
import Data.Tuple (Tuple)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Console (log)
import Foreign.Object (Object)
import Foreign.Object as Object

main :: Effect Unit
main = do
  log "-- array-index keys first, by value, then the others in insertion order"
  let mixed = Object.fromFoldable [ "b" /\ 1, "10" /\ 2, "a" /\ 3, "2" /\ 4, "01" /\ 5, "1" /\ 6 ]
  log (foldl (\shown value -> shown <> " " <> show value) "values:" mixed)
  log (foldlWithIndex (\key shown value -> shown <> " " <> key <> "=" <> show value) "entries:" mixed)
  log (foldr (\value shown -> show value <> " " <> shown) "(foldr)" mixed)
  log (foldrWithIndex (\key value shown -> key <> "=" <> show value <> " " <> shown) "(foldrWithIndex)" mixed)
  log (foldMap (\value -> [ value ]) mixed # show)
  log (show (sum mixed) <> " " <> show (Object.values mixed))
  log (show (Object.toUnfoldable mixed :: Array (Tuple String Int)))
  log (show (any (_ > 5) mixed) <> " " <> show (all (_ > 0) mixed) <> " " <> show (Object.all (\key _ -> key /= "a") mixed))
  for_ (Object.keys mixed) \key -> log ("key " <> key)
  log "-- duplicates keep their first position and their last value"
  let duplicated = Object.fromFoldable (Array.range 1 24 <#> \n -> keyOf n /\ n)
  log (foldlWithIndex (\key shown value -> shown <> " " <> key <> "=" <> show value) "entries:" duplicated)
  let words = [ "x", "y", "3", "x", "z", "y", "x", "0", "w", "v", "u", "t", "s", "3" ]
  let counted = Object.fromFoldableWith (+) (words <#> \word -> word /\ 1)
  log (foldlWithIndex (\key shown value -> shown <> " " <> key <> "=" <> show value) "counted:" counted)
  log (show (Object.size counted) <> " " <> show (Object.lookup "x" counted) <> " " <> show (Object.lookup "q" counted))
  log "-- nothing to visit"
  let empty = Object.fromFoldable ([] :: Array (Tuple String Int))
  log (foldl (\shown value -> shown <> " " <> show value) "values:" empty)
  log (show (sum empty) <> " " <> show (Object.keys empty) <> " " <> show (any (_ > 0) empty))
  log (show (foldlWithIndex (\key keys _ -> keys <> [ key ]) [] (Object.empty :: Object Unit)))
  where
  keyOf n = (if n `mod` 3 == 0 then "" else "k") <> show (n `mod` 10)
