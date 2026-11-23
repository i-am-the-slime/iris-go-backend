module Main where

import Prelude

import Control.Monad.ST (ST)
import Control.Monad.ST as ST
import Data.Array.ST (STArray)
import Data.Array.ST as STArray
import Data.Maybe (Maybe(..))

withCopy :: forall a. (forall region. STArray region a -> ST region Unit) -> Array a -> Array a
withCopy use xs = ST.run (STArray.withArray use xs)

sortBy :: forall a. (a -> a -> Ordering) -> Array a -> Array a
sortBy order = withCopy \array -> do
  length <- STArray.length array
  insertFrom array 1 length
  where
  insertFrom :: forall region. STArray region a -> Int -> Int -> ST region Unit
  insertFrom array i length = when (i < length) do
    sink array i
    insertFrom array (i + 1) length

  sink :: forall region. STArray region a -> Int -> ST region Unit
  sink array i = when (i > 0) do
    before <- STArray.peek (i - 1) array
    current <- STArray.peek i array
    case before, current of
      Just x, Just y | order x y == GT -> do
        void (STArray.poke (i - 1) y array)
        void (STArray.poke i x array)
        sink array (i - 1)
      _, _ -> pure unit

descending :: Int -> Int -> Ordering
descending x y = compare y x

numbers :: Array Int
numbers = [ 7, 3, 9, 1, 4, 8, 2, 6, 5, 0 ]

main :: Array String
main =
  [ show (sortBy compare numbers)
  , show (sortBy descending numbers)
  , show (sortBy compare ([] :: Array Int))
  ]
