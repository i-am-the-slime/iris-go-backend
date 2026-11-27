module Main where

import Prelude

import Control.Monad.ST (ST)
import Control.Monad.ST as ST
import Data.Array as Array
import Data.Array.ST (STArray)
import Data.Array.ST as STArray
import Data.Foldable (for_)
import Data.Maybe (Maybe(..), fromMaybe)

-- | The fewest steps of one or three stairs up to every stair.
stairs :: Int -> Array Int
stairs size = ST.run (STArray.withArray climb start)
  where
  start = Array.cons 0 (Array.replicate size size)
  stairsAbove = Array.drop 1 (Array.mapWithIndex (\stair _ -> stair) start)

  climb :: forall h. STArray h Int -> ST h Unit
  climb steps = for_ stairsAbove \stair -> do
    fromBelow <- stepFrom 1 stair steps
    fromFurther <- stepFrom 3 stair steps
    STArray.poke stair (min fromBelow fromFurther) steps

  stepFrom :: forall h. Int -> Int -> STArray h Int -> ST h Int
  stepFrom height stair steps = STArray.peek (stair - height) steps <#> case _ of
    Nothing -> size
    Just earlier -> earlier + 1

main :: Int
main = fromMaybe 0 (Array.last (stairs 1000))
