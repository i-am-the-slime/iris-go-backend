module Fun.SharedRecordMaps where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Effect (Effect)
import Effect.Console (log)
import Effect.Ref as Ref

main :: Effect Unit
main = do
  log "-- a record used twice keeps its map: each update sees the map before both"
  log (forked 6)
  log (forked 3)
  log "-- a record a closure captures"
  log (show (captured 6))
  log (show (captured 2))
  log "-- a record that is shown or compared"
  log (show (counted 4))
  log (show (counted 4 == counted 4))
  log (show (counted 4 == counted 5))
  log "-- a record kept in a ref"
  kept <- Ref.new (counted 3)
  Ref.modify_ (\record -> record { table = Map.insert 50 1 record.table }) kept
  later <- Ref.read kept
  log (show (Map.keys later.table))
  log "-- records put into an array"
  log (show (listed 3 <#> \record -> Map.keys record.table))
  log (show (listed 5 <#> \record -> Map.size record.table))

type Counted = { table :: Map Int Int, total :: Int }

counted :: Int -> Counted
counted count = foldl (\record n -> { table: Map.insert (n * 3) n record.table, total: record.total + n }) { table: Map.empty, total: 0 } (Array.range 1 count)

forked :: Int -> String
forked count = do
  let record = counted count
  let left = record { table = Map.insert 100 1 record.table }
  let right = record { table = Map.insert 200 2 record.table }
  show (Map.keys left.table) <> " " <> show (Map.keys right.table)

captured :: Int -> Array Boolean
captured count = do
  let record = counted count
  let present = \key -> Map.member key record.table
  let grown = record { table = Map.insert 7 7 record.table }
  (Array.range 5 9 <#> present) <> [ Map.member 7 grown.table ]

listed :: Int -> Array Counted
listed count = do
  let record = counted count
  [ record, record { table = Map.delete 3 record.table }, record { table = Map.insert 1 1 record.table } ]
