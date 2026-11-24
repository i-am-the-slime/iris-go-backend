module Fun.Perf where

import Prelude

import Control.Monad.Rec.Class (Step(..), tailRec, tailRecM)
import Control.Monad.ST as ST
import Control.Monad.ST.Ref as STRef
import Control.Monad.State (State, evalState, modify_, get)
import Data.Array ((..), foldl)
import Data.Array as Array
import Data.Foldable (for_, sum)
import Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.String (joinWith)
import Data.Tuple.Nested ((/\))
import Effect (Effect, forE)
import Effect.Aff (Aff, launchAff_)
import Effect.Class (liftEffect)
import Effect.Console (log)
import Effect.Ref as Ref
import Yoga.Om (Om)
import Yoga.Om as Om

limit :: Int
limit = 10000000

pureLoop :: Int -> Int
pureLoop n = tailRec step (0 /\ 0)
  where
  step (acc /\ i)
    | i >= n = Done acc
    | otherwise = Loop ((acc + i `mod` 7) /\ (i + 1))

stLoop :: Int -> Int
stLoop n = ST.run do
  total <- STRef.new 0
  ST.for 0 n \i -> STRef.modify (_ + i `mod` 3) total
  STRef.read total

stateLoop :: Int -> Int
stateLoop n = evalState (tailRecM step 0) 0
  where
  step :: Int -> State Int (Step Int Int)
  step i
    | i >= n = get <#> Done
    | otherwise = modify_ (_ + 1) $> Loop (i + 1)

affLoop :: Int -> Aff Int
affLoop n = tailRecM step 0
  where
  step i
    | i >= n = pure (Done i)
    | otherwise = pure (Loop (i + 1))

omLoop :: Int -> Om {} () Int
omLoop n = tailRecM step 0
  where
  step i
    | i >= n = pure (Done i)
    | otherwise = pure (Loop (i + 1))

main :: Effect Unit
main = do
  log $ show (pureLoop limit)
  log $ show (stLoop limit)
  log $ show (foldl (+) 0 (1 .. limit))
  log $ show (sum ((1 .. 1000000) <#> (_ * 2) # Array.filter (_ > 10)))
  counter <- Ref.new 0
  forE 0 limit \i -> Ref.modify_ (_ + i `mod` 5) counter
  Ref.read counter >>= show >>> log
  log $ show (stateLoop 1000000)
  let table = foldl (\m i -> Map.insert (i `mod` 1000) i m) Map.empty (1 .. 200000)
  log $ show (Map.size table) <> show (fromMaybe 0 (Map.lookup 7 table))
  log $ show (Array.length (Array.sort ((1 .. 300000) <#> \i -> (i * 7919) `mod` 100003)))
  log $ show (joinWith "" ((1 .. 100000) <#> show) # \s -> Array.length (Array.replicate 1 s))
  launchAff_ do
    n <- affLoop 1000000
    log (show n) # liftEffect
    m <- omLoop 1000000 # Om.runOm {} { exception: \_ -> pure (-1) }
    log (show m) # liftEffect
