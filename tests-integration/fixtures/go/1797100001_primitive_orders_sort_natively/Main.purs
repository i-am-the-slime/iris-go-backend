module Main where

import Prelude

import Data.Array as Array
import Data.Char (fromCharCode)
import Data.Maybe (fromMaybe)
import Data.Newtype (class Newtype)
import Data.Ord (comparing)
import Data.String.CodeUnits as String

newtype Score = Score Int

derive instance Newtype Score _
derive newtype instance Eq Score
derive newtype instance Ord Score

newtype Label = Label String

derive instance Eq Label
derive instance Ord Label

type Entry = { name :: String, rank :: Int, weight :: Number, initial :: Char }

entries :: Array Entry
entries =
  [ { name: "delta", rank: 2, weight: 0.5, initial: 'd' }
  , { name: "alpha", rank: 1, weight: -0.0, initial: 'a' }
  , { name: "echo", rank: 2, weight: 0.0, initial: 'e' }
  , { name: "bravo", rank: 1, weight: 0.0 / 0.0, initial: 'b' }
  , { name: "charlie", rank: 3, weight: 0.5, initial: 'c' }
  , { name: "foxtrot", rank: 1, weight: -1.0, initial: 'a' }
  ]

numbers :: Array Number
numbers = [ 3.0, -0.0, 0.0 / 0.0, 1.0 / 0.0, 0.0, -1.0 / 0.0, -2.5, 0.0 / 0.0, 0.0, -0.0, 7.25 ]

signs :: Array Number
signs = [ 0.0, -0.0, 1.0, -0.0, 0.0, -1.0 ]

surrogates :: Array String
surrogates =
  [ "\xFF61", "\x1F600", "b", "\xE000", "a\x1F600", "aa", "", "\xD83D", "\xDE00", "a", "\xD83D\xDE00", "\xFFFF" ]

signed :: Number -> String
signed n = if n == 0.0 then (if 1.0 / n < 0.0 then "-0" else "+0") else show n

byLength :: String -> String -> Ordering
byLength = comparing String.length

names :: Array Entry -> Array String
names = map _.name

main :: Array String
main =
  [ show (Array.sort [ 5, 3, -7, 3, 2147483647, -2147483648, 0 ])
  , show (Array.sort ([] :: Array Int))
  , show (Array.sortBy compare [ 9, 1, 8, 2 ])
  , show (Array.sortBy (flip compare) [ 9, 1, 8, 2 ])
  , show (Array.sort numbers)
  , show (signed <$> Array.sort signs)
  , show (Array.sort [ 'q', 'b', 'Z', 'a', fromMaybe 'a' (fromCharCode 0xD800), fromMaybe 'a' (fromCharCode 0xFFFF) ])
  , show (Array.sort [ "pear", "apple", "Banana", "", "apple" ])
  , show (Array.sort surrogates)
  , show (map (\(Score score) -> score) (Array.sort [ Score 4, Score 1, Score 3 ]))
  , show (map (\(Label label) -> label) (Array.sort [ Label "b", Label "a", Label "c" ]))
  , show (names (Array.sortWith _.rank entries))
  , show (names (Array.sortBy (comparing _.rank) entries))
  , show (names (Array.sortBy (comparing _.initial) entries))
  , show (names (Array.sortWith _.name entries))
  , show (names (Array.sortWith _.weight entries))
  , show (names (Array.sortWith (\entry -> entry.rank * 10 - String.length entry.name) entries))
  , show (Array.sortBy byLength [ "ccc", "a", "bb", "d", "" ])
  , show (Array.sortWith negate [ 3, 1, 2, 1 ])
  , String.fromCharArray (Array.sort (String.toCharArray "hello"))
  ]
