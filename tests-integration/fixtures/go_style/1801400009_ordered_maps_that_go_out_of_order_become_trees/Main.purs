module Fun.OutOfOrder where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl, foldr)
import Data.FoldableWithIndex (foldrWithIndex)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (type (/\))
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = do
  log "-- ascending for a while, then a key below the greatest, its least and greatest asked all along"
  log (show (turned 15))
  log (show (turned 18))
  log (show (turned 19))
  log (show (turned 300))
  log "-- the keys next to probes asked as the map turns: before, at and after the turn"
  log (show (probedAcrossTheTurn 120))
  log "-- the keys next to one past a long stretch of deleted keys"
  log (show (pastHoles 200))
  log "-- folded in order before and after the turn"
  log (show (folds 40 false))
  log (show (folds 40 true))
  log "-- updates of held and deleted keys below the greatest"
  log (show (Map.toUnfoldable (updated 60) :: Array (Int /\ Int)))

-- | The least and greatest keys after each insert of ascending keys that turn to descending ones.
turned :: Int -> Array String
turned count = (foldl step { shown: [], map: Map.empty } (Array.range 1 (count + 6))).shown
  where
  step { shown, map } n = do
    let key = if n <= count then n * 2 else (count + 6 - n) * 3
    let grown = Map.insert key n map
    let thinned = case Map.findMin grown of
          Just { key: least } | n `mod` 7 == 0 -> Map.delete least grown
          _ -> grown
    { shown: Array.snoc shown (show (_.key <$> Map.findMin thinned) <> show (_.key <$> Map.findMax thinned) <> show (Map.size thinned)), map: thinned }

probedAcrossTheTurn :: Int -> Array String
probedAcrossTheTurn count = (foldl step { shown: [], map: Map.empty } (Array.range 1 count)).shown
  where
  step { shown, map } n = do
    let key = if n < count / 2 then n * 4 else (n * 37) `mod` (count * 2)
    let grown = if n `mod` 5 == 0 then Map.delete (key - 4) map else Map.insert key n map
    let probe = (n * 13) `mod` (count * 2)
    let found = [ Map.lookupLT probe grown, Map.lookupLE probe grown, Map.lookupGE probe grown, Map.lookupGT probe grown ] <#> (_ <#> _.key)
    { shown: Array.snoc shown (show found), map: grown }

pastHoles :: Int -> Array String
pastHoles count = do
  let filled = foldl (\map n -> Map.insert n n map) Map.empty (Array.range 1 count)
  let holed = foldl (\map n -> Map.delete n map) filled (Array.range 20 180)
  let asked = [ Map.lookupLE 100 holed, Map.lookupGE 100 holed, Map.lookupLT 181 holed, Map.lookupGT 19 holed ]
  let grown = Map.insert 100 0 holed
  (asked <#> show) <> [ show (Map.findMin grown), show (Map.lookupGE 99 grown), show (Map.toUnfoldable grown :: Array (Int /\ Int)) ]

folds :: Int -> Boolean -> Array String
folds count turns = do
  let built = foldl (\map n -> Map.insert (n * 3) n map) Map.empty (Array.range 1 count)
  let queued = case Map.findMin built of
        Just { key } -> Map.delete key built
        Nothing -> built
  let shaped = if turns then Map.insert 7 (-7) queued else queued
  [ show (Map.keys shaped)
  , show (Map.values shaped)
  , foldr (\value text -> show value <> " " <> text) "" shaped
  , foldrWithIndex (\key value text -> show key <> "=" <> show value <> " " <> text) "" shaped
  ]

updated :: Int -> Map Int Int
updated count = do
  let built = foldl (\map n -> Map.insert n n map) Map.empty (Array.range 1 count)
  let queued = case Map.findMax built of
        Just { key } -> Map.delete key (Map.delete 30 built)
        Nothing -> built
  let rewritten = foldl (\map n -> Map.insert (n * 5) (-n) map) queued (Array.range 1 8)
  Map.insert 30 30 (Map.insert 0 0 rewritten)
