module Main where

import Prelude

import Control.Monad.ST (run)
import Data.Array.ST as STArray

-- The scrutinee `xs <> ys` is a call to array.Append, and `map f xs` one to
-- array.Map; named after those calls, the hoisted scrutinees would be
-- `append` and `map`, shadowing the builtin that push calls and the
-- keyword.
counted :: Array Int -> Array Int -> Array Int
counted xs ys = run do
  pushed <- STArray.new
  case xs <> ys of
    [] -> void (STArray.push 0 pushed)
    _ -> void (STArray.push 1 pushed)
  case map (_ * 2) xs of
    [ x ] -> void (STArray.push x pushed)
    _ -> pure unit
  STArray.unsafeFreeze pushed

main :: Array Int
main = counted [ 4 ] [ 5 ] <> counted [] []
