module Main where

import Prelude

import Control.Monad.ST (ST)
import Control.Monad.ST as ST
import Data.Array.ST (STArray)
import Data.Array.ST as STArray
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Console (log)

popWhileBelow :: forall h. Int -> Int -> STArray h Int -> ST h Int
popWhileBelow limit total stack =
  if total >= limit then pure total
  else STArray.pop stack >>= case _ of
    Just top -> popWhileBelow limit (total + top) stack
    Nothing -> pure total

pushCountdown :: forall h. Int -> STArray h Int -> ST h Unit
pushCountdown count stack =
  if count <= 0 then pure unit
  else do
    _ <- STArray.push count stack
    pushCountdown (count - 1) stack

shiftAndRequeue :: forall h. Int -> STArray h Int -> ST h Int
shiftAndRequeue total queue = STArray.shift queue >>= case _ of
  Just front -> do
    when (front < 3) (void (STArray.push (front + 10) queue))
    shiftAndRequeue (total * 2 + front) queue
  Nothing -> pure total

remainingAfterPops :: Array Int -> { total :: Int, rest :: Array Int }
remainingAfterPops values = ST.run do
  stack <- STArray.thaw values
  total <- popWhileBelow 10 0 stack
  rest <- STArray.freeze stack
  pure { total, rest }

countdown :: Int -> Array Int
countdown count = ST.run do
  stack <- STArray.new
  pushCountdown count stack
  _ <- STArray.push 0 stack
  STArray.freeze stack

requeued :: Array Int -> { total :: Int, left :: Array Int }
requeued values = ST.run do
  queue <- STArray.thaw values
  total <- shiftAndRequeue 0 queue
  left <- STArray.freeze queue
  pure { total, left }

main :: Effect Unit
main = do
  log (show (remainingAfterPops [ 1, 2, 3, 4, 5, 6 ]))
  log (show (remainingAfterPops [ 20 ]))
  log (show (remainingAfterPops []))
  log (show (countdown 3))
  log (show (countdown 0))
  log (show (requeued [ 1, 5, 2 ]))
