module Main where

import Prelude

import Control.Monad.ST as ST
import Data.Array.ST as STArray

twice :: forall a. a -> Array a
twice value = ST.run do
  array <- STArray.new
  _ <- STArray.push value array
  _ <- STArray.push value array
  STArray.unsafeFreeze array

main :: Array Int
main = (twice :: forall b. b -> Array b) 1 <> (twice :: forall b. b -> Array b) 2
