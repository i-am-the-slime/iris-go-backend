module Main where

import Prelude

import Effect (Effect)
import Effect.Exception (throw)
import Effect.Ref as Ref
import Partial.Unsafe (unsafeCrashWith)

scaled :: Int -> Int
scaled n
  | n > 100 = do
      let tripled = n * 3
      tripled + unsafeCrashWith "too large"
  | otherwise = n * 2

main :: Effect Int
main = do
  count <- Ref.new 1
  seen <- Ref.read count
  next <- Ref.modify (_ + 1) count
  when (seen > 5) do
    _ <- throw "too many"
    Ref.write next count
  pure (scaled seen)
