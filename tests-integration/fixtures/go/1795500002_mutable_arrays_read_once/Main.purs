module Main where

import Prelude

import Control.Monad.ST (ST, for, run)
import Data.Array.ST (STArray)
import Data.Array.ST as STA
import Data.Maybe (fromMaybe)

-- | Inlined into a loop, the modify tests its bound once: the write sits inside the read's test.
bump :: forall r. STArray r Number -> Int -> Number -> ST r Unit
bump array i by = void (STA.modify i (_ + by) array)

get :: forall r. STArray r Number -> Int -> ST r Number
get array i = fromMaybe 0.0 <$> STA.peek i array

-- | A helper too large to inline that only indexes its array takes the array's slice, and each
-- | modify tests its bound once.
smooth :: forall r. STArray r Number -> Int -> ST r Unit
smooth array i = do
  left <- get array (i - 1)
  here <- get array i
  right <- get array (i + 1)
  let average = (left + here + right) / 3.0
  bump array (i - 1) ((average - left) * 0.5)
  bump array i ((average - here) * 0.5)
  bump array (i + 1) ((average - right) * 0.5)
  edge <- get array (i + 2)
  when (edge > average) (bump array (i + 2) (average - edge))

-- | A push can replace the slice: every access after it reads the slice again.
pushThenRead :: forall r. STArray r Number -> ST r Number
pushThenRead array = do
  _ <- STA.push 9.0 array
  a <- get array 0
  n <- STA.push 10.0 array
  b <- get array (n - 1)
  pure (a + b)

-- | A helper that calls another action on the array reads it through the pointer.
bumpTwice :: forall r. STArray r Number -> Int -> ST r Unit
bumpTwice array i = do
  bump array i 1.0
  _ <- STA.push 0.0 array
  bump array i 1.0

-- | Bodies with one array per coordinate: the loop only indexes the arrays, so it reads each
-- | array's slice once before it starts.
pull :: Array String
pull = run do
  x <- STA.thaw [ 0.0, 1.0, 3.0 ]
  y <- STA.thaw [ 0.0, 2.0, -1.0 ]
  vx <- STA.thaw [ 0.0, 0.0, 0.0 ]
  vy <- STA.thaw [ 0.0, 0.5, 0.0 ]
  m <- STA.thaw [ 2.0, 1.0, 0.5 ]
  for 0 3 \_ -> do
    for 0 3 \i -> for 0 3 \j -> when (i /= j) do
      dx <- (-) <$> get x j <*> get x i
      dy <- (-) <$> get y j <*> get y i
      mj <- get m j
      bump vx i (dx * mj * 0.125)
      bump vy i (dy * mj * 0.125)
    for 0 3 \i -> do
      get vx i >>= \v -> bump x i (0.5 * v)
      get vy i >>= \v -> bump y i (0.5 * v)
  xs <- STA.freeze x
  ys <- STA.freeze y
  pure [ show xs, show ys ]

-- | Comparing strings calls a runtime helper of a pure operation: the loop still reads the
-- | array's slice once.
countBefore :: Array String
countBefore = run do
  words <- STA.thaw [ "pear", "apple", "fig" ]
  counts <- STA.thaw [ 0, 0, 0 ]
  for 0 3 \i -> for 0 3 \j -> do
    a <- fromMaybe "" <$> STA.peek i words
    b <- fromMaybe "" <$> STA.peek j words
    when (b < a) (void (STA.modify i (_ + 1) counts))
  frozen <- STA.freeze counts
  pure [ show frozen ]

-- | Sorting in the loop runs an effect, which could change any array: the loop reads even the
-- | array it only indexes through the pointer.
sortEach :: Array String
sortEach = run do
  xs <- STA.thaw [ 3, 1, 2 ]
  ys <- STA.thaw [ 0, 0 ]
  for 0 2 \i -> do
    _ <- STA.sortBy (\a b -> compare (b + i) a) xs
    first <- fromMaybe 0 <$> STA.peek 0 xs
    void (STA.modify i (_ + first) ys)
  sorted <- STA.freeze xs
  bumped <- STA.freeze ys
  pure [ show sorted, show bumped ]

-- | Indices out of range leave the array alone and read the default.
main :: Array String
main = run do
  xs <- STA.thaw [ 1.0, 2.0, 3.0 ]
  for 0 3 \i -> bump xs i (toNumber i)
  bump xs 7 1.0
  bump xs (-1) 1.0
  bumpTwice xs 1
  smooth xs 1
  smooth xs 2
  edge <- get xs 9
  total <- pushThenRead xs
  frozen <- STA.freeze xs
  pure ([ show frozen, show edge, show total ] <> pull <> countBefore <> sortEach)
  where
  toNumber i = if i == 0 then 0.0 else 1.0 + toNumber (i - 1)
