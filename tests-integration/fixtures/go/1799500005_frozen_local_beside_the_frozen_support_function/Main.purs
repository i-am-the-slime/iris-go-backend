module Main where

import Prelude

import Control.Monad.ST as ST
import Data.Array (length)
import Data.Array.ST as STArray
import Data.Foldable (for_)
import Data.Array ((..))
import Effect (Effect)
import Journal (log)

counted :: Int -> { values :: Array Int, size :: Int }
counted n = ST.run do
  array <- STArray.new
  for_ (1 .. n) \i -> STArray.push (i * i) array
  frozen <- STArray.unsafeFreeze array
  pure { values: frozen, size: length frozen }

main :: Effect Unit
main = do
  let { values, size } = counted 4
  log (show values <> " " <> show size)
