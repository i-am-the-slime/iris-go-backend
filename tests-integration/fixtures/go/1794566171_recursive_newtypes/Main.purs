module Main where

import Prelude

import Data.Maybe (Maybe(..))

type Level = { name :: String, minis :: Array Mini }

newtype Mini = Mini Level

names :: Level -> Array String
names level = [ level.name ] <> (level.minis >>= \(Mini mini) -> names mini)

newtype Step = Step (Int -> Maybe Step)

countSteps :: Step -> Int -> Int
countSteps (Step next) n = case next n of
  Nothing -> n
  Just step -> countSteps step (n + 1)

main :: Array String
main =
  names { name: "root", minis: [ Mini { name: "a", minis: [] } ] }
    <> [ show (countSteps (Step \n -> if n < 3 then Just (Step \_ -> Nothing) else Nothing) 0) ]
