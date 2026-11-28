module Main where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Maybe (Maybe(..), fromMaybe)
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = do
  log "-- a fold inserts into the array it owns"
  log (show (insertedEach (Array.range 1 12)))
  log (show (insertedEach [] == []))
  log "-- a fold deletes from an array it was handed, which stays as it was"
  let numbers = Array.range 10 25
  log (show (deletedHalf numbers))
  log (show numbers)
  log "-- insertion sort keeps its input"
  let shuffled = [ 5, 3, 9, 1, 7, 3, 8, 2, 6, 0, 4 ]
  log (show (foldl (flip Array.insert) [] shuffled))
  log (show shuffled)
  log "-- an array with room to grow, inserted into by a fold and extended elsewhere"
  let roomy = Array.snoc (Array.snoc (Array.snoc [] 1) 2) 3
  let inserted = foldl (\current number -> fromMaybe current (Array.insertAt 1 number current)) roomy [ 40, 50 ]
  let extended = Array.snoc roomy 4
  log (show inserted)
  log (show extended)
  log (show roomy)
  log "-- positions outside the array leave it as it was"
  log (show (foldl (\current position -> fromMaybe current (Array.insertAt position 0 current)) [ 1, 2 ] [ -1, 3, 2, 0 ]))
  log (show (foldl (\current position -> fromMaybe current (Array.deleteAt position current)) [ 1, 2, 3 ] [ -1, 3, 2, 0 ]))
  log (show (Array.insertAt 3 9 [ 1, 2 ]))
  log (show (Array.deleteAt 2 [ 1, 2 ]))
  log "-- single writes leave the array they start from"
  let small = [ 1, 2, 3 ]
  log (show (Array.insertAt 1 7 small))
  log (show (Array.deleteAt 1 small))
  log (show small)
  log "-- a tail-recursive function owns the array it passes itself"
  log (show (countdownInserts 6 []))
  log (show (countdownDeletes [ 1, 2, 3, 4, 5, 6, 7 ]))
  log "-- init and unsnoc share the array without letting appends through"
  let full = [ 1, 2, 3, 4 ]
  log (show (Array.snoc (fromMaybe [] (Array.init full)) 99))
  log (show full)
  log (show (Array.init ([] :: Array Int)))
  log (show (Array.init [ 1 ]))
  log (show (sumByLastInit 0 (Array.range 1 100)))
  log (show (sumByUnsnoc 0 (Array.range 1 100)))
  where
  insertedEach = foldl (\current number -> fromMaybe current (Array.insertAt ((number * 7) `mod` 5) number current)) []
  deletedHalf values = foldl (\current number -> fromMaybe current (Array.deleteAt (number `mod` Array.length current) current)) values (Array.take (Array.length values / 2) values)

countdownInserts :: Int -> Array Int -> Array Int
countdownInserts count current
  | count <= 0 = current
  | otherwise = countdownInserts (count - 1) (fromMaybe current (Array.insertAt (Array.length current / 2) count current))

countdownDeletes :: Array Int -> Array Int
countdownDeletes current = case Array.deleteAt 1 current of
  Just shorter | Array.length shorter > 2 -> countdownDeletes shorter
  Just shorter -> shorter
  Nothing -> current

sumByLastInit :: Int -> Array Int -> Int
sumByLastInit total remaining = case Array.last remaining, Array.init remaining of
  Just final, Just rest -> sumByLastInit (total + final) rest
  _, _ -> total

sumByUnsnoc :: Int -> Array Int -> Int
sumByUnsnoc total stack = case Array.unsnoc stack of
  Just { init, last } -> sumByUnsnoc (total + last) init
  Nothing -> total
