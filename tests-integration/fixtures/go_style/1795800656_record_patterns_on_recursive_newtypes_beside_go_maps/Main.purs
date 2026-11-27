module Fun.RecursiveNewtype where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map as Map
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = do
  log "-- a recursive newtype of a record, taken apart by a record pattern, next to a Go map"
  log (show (taken 5 (countingFrom 3)))
  log (show (Map.size (squares 6)))

newtype Stream = Stream { head :: Int, rest :: Unit -> Stream }

countingFrom :: Int -> Stream
countingFrom n = Stream { head: n, rest: \_ -> countingFrom (n + 1) }

taken :: Int -> Stream -> Array Int
taken count (Stream { head, rest })
  | count <= 0 = []
  | otherwise = Array.cons head (taken (count - 1) (rest unit))

squares :: Int -> Map.Map Int Int
squares count = foldl (\table n -> Map.insert n (n * n) table) Map.empty (Array.range 1 count)
