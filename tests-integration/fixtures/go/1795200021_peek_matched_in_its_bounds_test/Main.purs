module Main where

import Prelude

import Control.Monad.ST (ST, for, run)
import Data.Array.ST (STArray)
import Data.Array.ST as STArray
import Data.Maybe (Maybe(..), fromMaybe)

-- A peek whose Maybe is matched at once is its bounds test: the default
-- is the else branch, and no Maybe is built.
peekOrZero :: forall region. Int -> STArray region Int -> ST region Int
peekOrZero i array = map (fromMaybe 0) (STArray.peek i array)

-- modify matches the peek with actions: the poke sits inside the bounds
-- test of the peek, which Go then proves for the store.
masked :: forall region. Int -> STArray region Int -> ST region Unit
masked n array = for 0 n \i -> void (STArray.modify i (_ `mod` 7) array)

-- A constant negative index is the Nothing alternative alone.
before :: forall region. STArray region Int -> ST region Int
before array = STArray.peek (-1) array >>= case _ of
  Just x -> pure x
  Nothing -> pure (-1)

main :: Array Int
main = run do
  array <- STArray.thaw [ 10, 20, 30 ]
  masked 3 array
  first <- peekOrZero 0 array
  missing <- peekOrZero 5 array
  none <- before array
  elements <- STArray.unsafeFreeze array
  pure (elements <> [ first, missing, none ])
