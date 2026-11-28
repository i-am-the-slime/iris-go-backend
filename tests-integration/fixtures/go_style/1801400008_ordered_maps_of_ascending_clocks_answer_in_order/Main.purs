module Fun.AscendingClocks where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl, foldr, sum)
import Data.FoldableWithIndex (foldlWithIndex)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (type (/\))
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = do
  let recent = remembered 3000
  log "-- the keys used last of a cache of 40, by when they were used"
  log (show (Map.toUnfoldable recent.byLastUse :: Array (Int /\ Int)))
  log (show (Map.findMin recent.byLastUse) <> " " <> show (Map.findMax recent.byLastUse) <> " " <> show (Map.size recent.byLastUse))
  log "-- folded in order"
  log (show (foldl (\text key -> text <> show key <> ",") "" recent.byLastUse))
  log (show (foldr (\key text -> show key <> "," <> text) "" recent.byLastUse))
  log (show (foldlWithIndex (\time total key -> total + time * key) 0 recent.byLastUse) <> " " <> show (sum recent.byLastUse))
  log "-- the clocks next to probes as the cache goes: held, deleted, before the first and after the last"
  log (show recent.probed)
  log "-- clocks that count by threes and by thousands, the oldest evicted"
  log (show (Map.toUnfoldable (counted 3 200) :: Array (Int /\ Int)))
  log (show (Map.toUnfoldable (counted 1000 200) :: Array (Int /\ Int)))
  log "-- emptied, then filled again"
  log (show (Map.toUnfoldable (refilled 50) :: Array (Int /\ Int)))

type Recent = { clock :: Int, byKey :: Map Int Int, byLastUse :: Map Int Int, probed :: Array String }

-- | A cache of the 40 keys used last, which forgets a key's old use whenever it is used again.
remembered :: Int -> Recent
remembered count = foldl use { clock: 0, byKey: Map.empty, byLastUse: Map.empty, probed: [] } (Array.range 1 count)
  where
  use recent n = do
    let key = (n * n * 7 + n * 3) `mod` 61
    let forgotten = case Map.lookup key recent.byKey of
          Just lastUsed -> Map.delete lastUsed recent.byLastUse
          Nothing -> recent.byLastUse
    let evicted = case Map.findMin forgotten of
          Just { key: oldest, value: oldestKey } | Map.size forgotten >= 40 && not (Map.member key recent.byKey) ->
            { byKey: Map.delete oldestKey recent.byKey, byLastUse: Map.delete oldest forgotten }
          _ -> { byKey: recent.byKey, byLastUse: forgotten }
    let byLastUse = Map.insert recent.clock key evicted.byLastUse
    { clock: recent.clock + 1
    , byKey: Map.insert key recent.clock evicted.byKey
    , byLastUse
    , probed: if n > count - 40 then Array.snoc recent.probed (nextTo (recent.clock - 50 + (n * 7) `mod` 60) byLastUse) else recent.probed
    }

nextTo :: Int -> Map Int Int -> String
nextTo probe map = show (_.key <$> Map.lookupLT probe map) <> show (_.key <$> Map.lookupLE probe map) <> show (_.key <$> Map.lookupGE probe map) <> show (_.key <$> Map.lookupGT probe map)

counted :: Int -> Int -> Map Int Int
counted step count = foldl tick Map.empty (Array.range 1 count)
  where
  tick map n = do
    let grown = Map.insert (n * step) n map
    if n `mod` 3 == 0 then case Map.findMin grown of
      Just { key } -> Map.delete key grown
      Nothing -> grown
    else grown

refilled :: Int -> Map Int Int
refilled count = do
  let filled = foldl (\map n -> Map.insert n n map) Map.empty (Array.range 1 count)
  let emptied = foldl (\map _ -> drop map) filled (Array.range 1 count)
  foldl (\map n -> Map.insert (n * 2) n map) emptied (Array.range 1 count)
  where
  drop map = case Map.findMax map of
    Just { key } -> Map.delete key map
    Nothing -> map
