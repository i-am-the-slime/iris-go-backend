module Main where

import Prelude

import Unsafe.Coerce (unsafeCoerce)

data Failure (e :: Row Type) = Failure String

newtype M (e :: Row Type) a = M (forall c. Int -> ((Unit -> c) -> c) -> (Failure e -> c) -> (a -> c) -> c)

data Step a = More (Unit -> Step a) | Stop String | Done a

pureM :: forall e a. a -> M e a
pureM a = M \_ _ _ done -> done a

bindM :: forall e a b. M e a -> (a -> M e b) -> M e b
bindM (M m) f = M \env more failure done ->
  more \_ -> m env more failure \a -> case f a of
    M n -> more \_ -> n env more failure done

ask :: forall e. M e Int
ask = M \env _ _ done -> done env

local :: forall e. (Int -> Int) -> M e ~> M e
local f (M k) = M \env more failure done -> k (f env) more failure done

anyFailure :: forall e. M () ~> M e
anyFailure = unsafeCoerce

run :: forall e a. Int -> M e a -> Step a
run env (M k) = go (k env More (\(Failure message) -> Stop message) Done)
  where
  go = case _ of
    More next -> go (next unit)
    step -> step

countdown :: Int -> M () Int
countdown n
  | n <= 0 = ask
  | otherwise = bindM ask \_ -> countdown (n - 1)

loop :: Int -> Int -> M (parse :: String) Int
loop i total
  | i <= 0 = pureM total
  | otherwise =
      bindM (ask # local (_ + i)) \shifted ->
        bindM (anyFailure (countdown (i `mod` 3))) \counted ->
          loop (i - 1) ((total + shifted + counted) `mod` 1000003)

finished :: Step Int -> Int
finished = case _ of
  Done value -> value
  Stop _ -> -1
  More _ -> -2

main :: Array Int
main = [ finished (run 0 (loop 30 0)) ]
