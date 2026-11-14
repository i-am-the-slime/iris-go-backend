module Main where

import Prelude

newtype Lazy a = Lazy (Unit -> a)

defer :: forall a. (Unit -> a) -> Lazy a
defer = Lazy

force :: forall a. Lazy a -> a
force (Lazy f) = f unit

buildThunks :: Int -> Lazy Int -> Lazy Int
buildThunks 0 acc = acc
buildThunks n acc = buildThunks (n - 1) (defer \_ -> force acc + 1)

countDown :: Int -> (Int -> Int) -> Int
countDown 0 k = k 0
countDown n k
  | n `mod` 2 == 0 = countDown (n - 1) \x -> k (x + n)
  | otherwise = countDown (n - 1) \x -> k (x * 2)

main :: { forced :: Int, continued :: Int }
main =
  { forced: force (buildThunks 1000 (defer \_ -> 0))
  , continued: countDown 10 \x -> x - 1
  }
