module Fun.Zips where

import Prelude

import Data.Array as Array
import Data.Foldable (sum)
import Effect (Effect)
import Effect.Console (log)

data Operation = Get Int | Put Int Int

instance Show Operation where
  show (Get key) = "Get " <> show key
  show (Put key value) = "Put " <> show key <> " " <> show value

main :: Effect Unit
main = do
  log "-- three arrays zipped through a partially applied function, as long as the shortest"
  log (show (operations 8))
  log "-- four arrays, the function a top-level one, an operand mapped on its way"
  log (show (Array.zipWith ($) (Array.zipWith ($) (Array.zipWith weigh [ 1, 2, 3 ] [ 10, 20, 30, 40 ]) ((_ * 2) <$> [ 5, 6, 7 ])) [ 100, 200 ]))
  log "-- the application written out as a lambda"
  log (show (Array.zipWith (\step value -> step value) (Array.zipWith (\a b c -> a <> b <> c) [ "a", "b" ] [ "c", "d" ]) [ "e", "f", "g" ]))
  log "-- the sum of a long zip of three ranges"
  log (show (sum (weight <$> operations 10000)))
  log "-- a zip of functions that each take one more argument"
  log (show (Array.zipWith ($) (Array.zipWith (\a b -> \c -> a * b - c) [ 3, 4 ] [ 5, 6 ]) [ 1, 2 ]))
  where
  operations count = Array.zipWith ($) (Array.zipWith operation (Array.range 1 count) (Array.range 2 (count + 1))) (Array.range 3 (count + 2))
  operation kind key value = if kind < 4 then Get key else Put key value

weigh :: Int -> Int -> Int -> Int -> Int
weigh a b c d = a + b * c - d

weight :: Operation -> Int
weight (Get key) = key
weight (Put key value) = key + value
