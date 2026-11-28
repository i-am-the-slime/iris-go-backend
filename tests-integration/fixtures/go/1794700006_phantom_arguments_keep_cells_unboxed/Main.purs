module Main where

import Prelude

data Step r a = More (Unit -> Step r a) | Done a

newtype Count a = Count (forall c. ((Unit -> c) -> c) -> (a -> c) -> c)

pureCount :: forall a. a -> Count a
pureCount a = Count \_ done -> done a

bindCount :: forall a b. Count a -> (a -> Count b) -> Count b
bindCount (Count m) f = Count \more done ->
  more \_ -> m more \a -> case f a of
    Count n -> more \_ -> n more done

run :: forall a. Count a -> a
run (Count k) = go (k More Done)
  where
  go = case _ of
    More next -> go (next unit)
    Done a -> a

countdown :: Int -> Int -> Count Int
countdown n total
  | n <= 0 = pureCount total
  | otherwise = bindCount (pureCount n) \m -> countdown (n - 1) (total + m)

main :: Array Int
main = [ run (countdown 10 0) ]
