module Main where

import Prelude

import Control.Monad.ST as ST
import Control.Monad.ST.Ref as STRef
import Data.Array (any, foldl)

tripled :: Int -> Int
tripled x = ST.run do
  ref <- STRef.new x
  _ <- STRef.modify (_ * 3) ref
  STRef.read ref

countdown :: Int -> Int -> Int
countdown n acc = if n <= 0 then acc else countdown (n - 1) (tripled acc)

ignore :: Int -> Int
ignore _ = 0

numbers :: Array Int
numbers = [ 3, 1, 4, 1, 5, 9, 2, 6 ]

-- | A callback whose only mutation is a local `ST.run` is pure: `map` fuses into the fold and into
-- `any`, and an ignored argument that only runs one is dropped.
main :: { sum :: Int, found :: Boolean, counted :: Int, ignored :: Int }
main =
  { sum: foldl (+) 0 (map tripled numbers)
  , found: any (_ > 20) (map tripled numbers)
  , counted: foldl (+) 0 (map (\x -> ST.run (STRef.new x >>= \ref -> STRef.modify (_ + 1) ref)) numbers)
  , ignored: ignore (countdown 1 3)
  }
