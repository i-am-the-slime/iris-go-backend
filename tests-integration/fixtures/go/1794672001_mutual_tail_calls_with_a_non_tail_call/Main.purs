module Main where

import Prelude

-- `branch` calls `depth` in tail position and also not: that call goes through `depth`'s entry.
depth :: Int -> Int -> Int
depth acc n
  | n <= 0 = acc
  | n `mod` 2 == 0 = branch acc n
  | otherwise = depth (acc + 1) (n - 1)

branch :: Int -> Int -> Int
branch acc n = depth (acc + depth 0 (n / 4)) (n - 1)

-- Three members; `c` captures its parameter in a closure.
a :: Int -> String -> String
a n s = if n <= 0 then s else b (n - 1) (s <> "a")

b :: Int -> String -> String
b n s = if n <= 0 then s else c (show n) (n - 1)

c :: String -> Int -> String
c label n = do
  let prefix x = label <> x
  a n (prefix "c")

main :: { depth :: Int, letters :: String }
main = { depth: depth 0 30, letters: a 7 "" }
