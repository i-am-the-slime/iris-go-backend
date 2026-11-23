module Main where

import Prelude

import Control.Monad.ST (ST)
import Control.Monad.ST as ST
import Data.Array as Array
import Data.Array.ST (STArray)
import Data.Array.ST as STArray
import Data.Maybe (Maybe(..))

data List a = Nil | Cons a (List a)

sortBy :: forall a. (a -> a -> Ordering) -> Array a -> Array a
sortBy order xs = ST.run (STArray.withArray (\array -> quicksort array 0 (Array.length xs - 1)) xs)
  where
  quicksort :: forall region. STArray region a -> Int -> Int -> ST region Unit
  quicksort array low high = when (low < high) do
    pivotIndex <- partition array low high
    quicksort array low (pivotIndex - 1)
    quicksort array (pivotIndex + 1) high

  partition :: forall region. STArray region a -> Int -> Int -> ST region Int
  partition array low high = STArray.peek high array >>= case _ of
    Just pivot -> do
      pivotIndex <- partitionFrom array pivot high low low
      swap array pivotIndex high
      pure pivotIndex
    Nothing -> pure low

  partitionFrom :: forall region. STArray region a -> a -> Int -> Int -> Int -> ST region Int
  partitionFrom array pivot high i j
    | j < high = STArray.peek j array >>= case _ of
        Just value
          | order value pivot /= GT -> do
              swap array i j
              partitionFrom array pivot high (i + 1) (j + 1)
          | otherwise -> partitionFrom array pivot high i (j + 1)
        Nothing -> pure i
    | otherwise = pure i

  swap :: forall region. STArray region a -> Int -> Int -> ST region Unit
  swap array i j = do
    atI <- STArray.peek i array
    atJ <- STArray.peek j array
    case atI, atJ of
      Just x, Just y -> do
        void (STArray.poke i y array)
        void (STArray.poke j x array)
      _, _ -> pure unit

insertBy :: forall a. (a -> a -> Ordering) -> a -> List a -> List a
insertBy order x = case _ of
  Nil -> Cons x Nil
  Cons y rest
    | order x y == GT -> Cons y (insertBy order x rest)
    | otherwise -> Cons x (Cons y rest)

insertionSortBy :: forall a. (a -> a -> Ordering) -> List a -> List a
insertionSortBy order = go Nil
  where
  go sorted = case _ of
    Nil -> sorted
    Cons x rest -> go (insertBy order x sorted) rest

descending :: Int -> Int -> Ordering
descending x y = compare y x

byDistanceFrom :: Int -> Int -> Int -> Ordering
byDistanceFrom origin x y = compare (distance x) (distance y)
  where
  distance value = if value < origin then origin - value else value - origin

fromArray :: forall a. Array a -> List a
fromArray = Array.foldr Cons Nil

toArray :: forall a. List a -> Array a
toArray = case _ of
  Nil -> []
  Cons x rest -> Array.cons x (toArray rest)

numbers :: Array Int
numbers = [ 7, 3, 9, 1, 4, 8, 2, 6, 5, 0 ]

main :: Array String
main =
  [ show (sortBy compare numbers)
  , show (sortBy descending numbers)
  , show (sortBy (byDistanceFrom 4) numbers)
  , show (sortBy (comparing negate) numbers)
  , show (toArray (insertionSortBy compare (fromArray numbers)))
  , show (toArray (insertionSortBy descending (fromArray numbers)))
  , show (toArray (insertionSortBy (byDistanceFrom 6) (fromArray numbers)))
  ]
