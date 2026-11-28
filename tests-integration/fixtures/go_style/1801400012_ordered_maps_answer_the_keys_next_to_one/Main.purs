module Fun.NextKeys where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), isNothing)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = do
  log "-- a calendar that books an interval when the intervals next to its start leave room"
  log (show (booked [ 10 /: 20, 15 /: 25, 20 /: 30, 5 /: 10, 0 /: 6, 25 /: 27, 30 /: 31, 1 /: 2, 40 /: 50, 31 /: 40 ]))
  log "-- the keys next to each probe, as keys come and go"
  log (show (neighbours 30))
  log "-- floors and ceilings of keys below, between and above every key"
  log (show (bounds [ -5, 0, 3, 4, 10, 11, 99, 100, 101 ] (Map.fromFoldable [ 0 /\ "zero", 4 /\ "four", 10 /\ "ten", 100 /\ "hundred" ])))
  log "-- the keys next to a key of an empty map"
  log (show (Map.lookupLE 3 (Map.delete 3 (Map.singleton 3 3))) <> show (Map.lookupGT 3 (Map.delete 3 (Map.singleton 3 3))))

infix 5 Interval as /:

data Interval = Interval Int Int

-- | Books each interval unless it overlaps one booked before, by the booked interval starting
-- | at or before its start and the one starting after it.
booked :: Array Interval -> Array Boolean
booked = _.answers <<< foldl book { answers: [], calendar: Map.empty }
  where
  book { answers, calendar } (Interval start end) = do
    let before = Map.lookupLE start calendar
    let after = Map.lookupGT start calendar
    let free = fitsAfter before && fitsBefore after
    { answers: Array.snoc answers free, calendar: if free then Map.insert start end calendar else calendar }
    where
    fitsAfter = case _ of
      Nothing -> true
      Just { value: bookedEnd } -> bookedEnd <= start
    fitsBefore = case _ of
      Nothing -> true
      Just { key: bookedStart } -> end <= bookedStart

neighbours :: Int -> Array String
neighbours count = (foldl step { shown: [], map: Map.empty } (Array.range 1 count)).shown
  where
  step { shown, map } n = do
    let key = (n * 11) `mod` 37
    let changed = if n `mod` 3 == 0 then Map.delete ((n * 7) `mod` 37) map else Map.insert key n map
    let probe = (n * 5) `mod` 37
    { shown: Array.snoc shown (show (Map.lookupLT probe changed) <> show (Map.lookupLE probe changed) <> show (Map.lookupGE probe changed) <> show (Map.lookupGT probe changed)), map: changed }

bounds :: Array Int -> Map Int String -> Array String
bounds probes map = probes <#> \probe -> show (Map.lookupLE probe map) <> " " <> show (Map.lookupGE probe map) <> " " <> show (isNothing (Map.lookupLT probe map))
