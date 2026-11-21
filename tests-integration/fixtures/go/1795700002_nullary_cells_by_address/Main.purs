module Main where

import Prelude

import Data.Maybe (Maybe(..))

data Route = Home | Away | Trip Int Route

data Empty = Stop | Go Unit

legs :: Route -> Int
legs = case _ of
  Home -> 0
  Away -> 100
  Trip n rest -> n + legs rest

endsAway :: Route -> Boolean
endsAway = case _ of
  Trip _ rest -> endsAway rest
  Away -> true
  Home -> false

firstLeg :: Route -> Maybe Route
firstLeg = case _ of
  Trip n _ -> Just (Trip n Home)
  _ -> Nothing

goes :: Empty -> Boolean
goes = case _ of
  Go _ -> true
  Stop -> false

main :: { legs :: Int, away :: Boolean, first :: Int, goes :: Boolean }
main =
  { legs: legs (Trip 1 (Trip 2 Away))
  , away: endsAway (Trip 1 Away)
  , first: case firstLeg (Trip 3 Home) of
      Just route -> legs route
      Nothing -> -1
  , goes: goes (Go unit)
  }
