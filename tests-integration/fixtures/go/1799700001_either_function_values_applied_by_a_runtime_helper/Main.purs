module Main where

import Prelude

import Data.Either (Either(..))
import Effect (Effect)
import Journal (log)

tenfoldAboveOne :: Int -> Either Int Int
tenfoldAboveOne x = if x > 1 then Right (x * 10) else Left x

main :: Effect Unit
main = do
  let applied = [ tenfoldAboveOne, \x -> Left (x + 100) ] <*> [ 1, 2, 3 ]
  log (show applied)
