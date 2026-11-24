module T.Colls where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.FoldableWithIndex (foldrWithIndex, foldlWithIndex)
import Data.Foldable (foldMap, foldr, sum)
import Data.HashMap as HashMap
import Data.HashSet as HashSet
import Data.List (List(..), (:))
import Data.List as List
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Semigroup.Foldable (foldMap1)
import Data.Set as Set
import Data.Tuple (Tuple)
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Effect.Console (log)
import Foreign.Object as Object

main :: Effect Unit
main = do
  let wordCounts = [ "b", "a", "c", "a", "b", "a" ] # foldr (\w -> Map.insertWith (+) w 1) Map.empty
  log (show wordCounts)
  log (show (Map.unionWith (+) wordCounts (Map.fromFoldable [ "a" /\ 100, "z" /\ 1 ])))
  log (show (Map.alter (map (_ * 10)) "a" wordCounts) <> show (Map.alter (const (Just 0)) "q" wordCounts) <> show (Map.alter (const Nothing) "b" wordCounts))
  log (show (Map.toUnfoldable wordCounts :: Array (String /\ Int)))
  log (show (Map.toUnfoldable wordCounts :: List (Tuple String Int)))
  log (show (Map.keys wordCounts) <> show (Array.fromFoldable (Map.values wordCounts)))
  log (show (Map.lookup "c" wordCounts) <> show (Map.lookup "nope" wordCounts))
  log (foldrWithIndex (\k v acc -> k <> show v <> acc) "" wordCounts)
  log (foldlWithIndex (\k acc v -> acc <> k <> show v) "" wordCounts)
  log (show (Map.filterWithKey (\k v -> k /= "a" && v > 0) wordCounts))
  let negKeys = Map.fromFoldable [ (-5) /\ "m5", 3 /\ "p3", 0 /\ "z", (-10) /\ "m10" ]
  log (show negKeys <> show (Map.findMin negKeys) <> show (Map.findMax negKeys))
  log (show (Map.toUnfoldable (Map.fromFoldable [ (1 /\ "b") /\ 1, (0 /\ "z") /\ 2, (1 /\ "a") /\ 3 ]) :: Array ((Int /\ String) /\ Int)))
  -- Object: JS objects order integer-like keys ascending first, then strings in insertion order
  let obj = Object.fromFoldable [ "zeta" /\ 1, "10" /\ 2, "alpha" /\ 3, "2" /\ 4, "-1" /\ 5, "01" /\ 6, "1.5" /\ 7, "4294967295" /\ 8, "4294967294" /\ 9 ]
  log (show obj)
  log (show (Object.toUnfoldable obj :: Array (String /\ Int)))
  log (show (Object.keys obj) <> show (Object.values obj))
  log (show (Object.toAscUnfoldable obj :: Array (String /\ Int)))
  log (Object.foldMap (\k v -> k <> "=" <> show v <> ";") obj)
  log (show (Object.lookup "alpha" obj) <> show (Object.size obj) <> show (Object.member "2" obj))
  let obj2 = obj # Object.insert "beta" 10 # Object.delete "zeta" # Object.insert "0" 11 # Object.alter (map (_ + 1)) "alpha"
  log (show obj2)
  log (show (Object.union obj2 (Object.singleton "zeta" 99)))
  log (show (Object.filterWithKey (\k _ -> k > "1") obj2))
  log (show (map (_ * 2) obj2 # Object.toArrayWithKey (\k v -> k <> ":" <> show v)))
  log (show (Object.fromHomogeneous { b: 1, a: 2, "3": 3 }))
  -- HashMap
  let hm = HashMap.fromArray [ "x" /\ 1, "y" /\ 2, "x" /\ 3 ]
  log (show (HashMap.lookup "x" hm) <> show (HashMap.size hm) <> show (Array.sort (HashMap.keys hm)))
  log (show (Array.sort (HashMap.toArrayBy (/\) (HashMap.insertWith (+) "y" 40 hm))))
  log (show (HashSet.size (HashSet.fromArray [ 1, 2, 2, 3 ])) <> show (HashSet.member 2 (HashSet.fromArray [ 1, 2 ])))
  -- Set
  let primes = Set.fromFoldable [ 7, 2, 5, 3, 2, -1 ]
  log (show primes <> show (Set.member 5 primes) <> show (Set.toUnfoldable primes :: Array Int))
  log (show (Set.union primes (Set.fromFoldable [ 100 ])) <> show (Set.difference primes (Set.singleton 2)) <> show (Set.intersection primes (Set.fromFoldable [ 3, 4, 5 ])))
  log (show (Set.map (_ `mod` 3) primes))
  -- NonEmptyArray
  case NEA.fromArray [ 3, 1, 2 ] of
    Nothing -> log "empty?"
    Just nea -> do
      log (show nea <> show (NEA.head nea) <> show (NEA.last nea))
      log (show (NEA.cons' 0 [ 9, 8 ]) <> show (NEA.toArray (nea <#> (_ * 2))))
      log (show (foldMap1 show nea) <> show (NEA.sort nea) <> show (NEA.length nea))
      log (show (Array.groupBy (\a b -> a `mod` 2 == b `mod` 2) [ 1, 3, 2, 4, 5 ]))
  log (show (NEA.fromArray ([] :: Array Int)))
  -- List
  let list = 1 : 2 : 3 : Nil
  log (show list <> show (List.reverse list) <> show (Array.fromFoldable list) <> show (List.fromFoldable [ 4, 5 ]))
  log (show (List.sort (List.fromFoldable [ 3, -1, 2 ])) <> show (sum list))
  -- nested tuples
  let quad = 1 /\ "two" /\ 3.0 /\ [ 'f' ]
  case quad of
    a /\ b /\ c /\ d -> log (show a <> b <> show c <> show d)
  log (show quad)
  let triples = [ 1 /\ "a" /\ true, 2 /\ "b" /\ false ]
  triples <#> (\(n /\ s /\ flag) -> if flag then s else show n) # show # log
  let nestedMap :: Map String (Map Int (Array String))
      nestedMap = Map.fromFoldable [ "outer" /\ Map.fromFoldable [ 2 /\ [ "x" ], 1 /\ [] ] ]
  log (show nestedMap)
  log (show (Map.lookup "outer" nestedMap >>= Map.lookup 2 # fromMaybe []))
