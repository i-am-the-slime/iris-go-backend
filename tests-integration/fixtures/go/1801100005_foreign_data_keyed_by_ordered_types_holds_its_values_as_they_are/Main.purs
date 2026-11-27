module Main where

import Prelude

import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Effect (Effect)
import Table (Table)
import Table as Table

type Edge = { from :: Int, to :: Int }

type Placed = { name :: String, at :: { x :: Int, y :: Int } }

main :: Effect (Array String)
main = do
  byOrigin <- Table.empty :: Effect (Table Int (Array Edge))
  Table.insert 1 [ { from: 1, to: 2 }, { from: 1, to: 3 } ] byOrigin
  fromOne <- Table.lookup 1 byOrigin
  grid <- Table.empty :: Effect (Table Int (Array (Array Int)))
  Table.insert 0 [ [ 1, 2 ], [ 3 ] ] grid
  rows <- Table.values grid
  chosen <- Table.empty :: Effect (Table String (Maybe Edge))
  Table.insert "some" (Just { from: 4, to: 5 }) chosen
  Table.insert "none" Nothing chosen
  choices <- Table.values chosen
  places <- Table.empty :: Effect (Table Int Placed)
  Table.insert 7 { name: "seven", at: { x: 1, y: 2 } } places
  seven <- Table.lookup 7 places
  pure
    [ show (map _.to (fromMaybe [] fromOne))
    , show rows
    , show (map (maybe 0 _.to) choices)
    , maybe "" (\{ name, at } -> name <> show at.x <> show at.y) seven
    ]
