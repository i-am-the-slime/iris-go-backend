module Main where

import Prelude

import Data.Array (sort, zipWith)

data Suit = Hearts | Spades | Clubs

derive instance Eq Suit
derive instance Ord Suit

instance Show Suit where
  show Hearts = "hearts"
  show Spades = "spades"
  show Clubs = "clubs"

type Card = { rank :: Int, suit :: Suit }

-- | `show` of an enumeration stays one function for its calls with suits the caller cannot tell.
describe :: Card -> String
describe card = show card.rank <> " of " <> show card.suit

-- | Equality of an enumeration is Go's `==`, and of a record of comparable fields the struct's.
sameCard :: Card -> Card -> Boolean
sameCard a b = a == b

-- | `compare` of an enumeration compares the constants, which count up in declaration order.
ordered :: Suit -> Suit -> Ordering
ordered = compare

-- | Comparing with a known constructor still chooses by what chose it.
isGreater :: Int -> Int -> Boolean
isGreater x y = compare x y == GT

isSpades :: Suit -> Boolean
isSpades suit = suit == Spades

data Expression = Leaf Int | Add Expression Expression

-- | A `where` helper that only hands its arguments on is the function it calls.
scaled :: Int -> Expression -> Int
scaled factor = case _ of
  Leaf n -> n * factor
  Add left right -> scaledOf left + scaledOf right
  where
  scaledOf expression = scaled factor expression

suits :: Array Suit
suits = [ Clubs, Hearts, Spades ]

cards :: Array Card
cards = map (\suit -> { rank: 7, suit }) suits

main :: Array String
main =
  [ show (map describe cards)
  , show (zipWith sameCard cards (sort cards))
  , show (map show (sort suits))
  , show (zipWith ordered suits (sort suits))
  , show (zipWith isGreater [ 3, 1 ] [ 2, 2 ])
  , show (map (scaled 3) [ Add (Leaf 1) (Add (Leaf 2) (Leaf 3)) ])
  , show (map isSpades suits)
  ]
