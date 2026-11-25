module Main where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Ref as Ref
import Journal (log)

main :: Effect Unit
main = do
  count <- Ref.new 3 >>= Ref.read
  case Array.last (keptEvery 2 count) of
    Just latest -> log (show (latest * 2))
    Nothing -> log "empty"

keptEvery :: Int -> Int -> Array Int
keptEvery interval count = countdown count 0 []
  where
  countdown n total kept
    | n <= 0 = Array.snoc kept total
    | otherwise = do
        let next = total + n
        countdown (n - 1) next (keepAt n next kept)

  keepAt n value kept
    | n `mod` interval == 0 = Array.snoc kept value
    | otherwise = kept
