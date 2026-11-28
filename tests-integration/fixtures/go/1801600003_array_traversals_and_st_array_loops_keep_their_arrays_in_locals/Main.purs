module Main where

import Prelude

import Control.Monad.ST (ST)
import Control.Monad.ST as ST
import Data.Array.ST (STArray)
import Data.Array.ST as STArray
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)

halved :: Int -> Maybe Int
halved number = if number `mod` 2 == 0 then Just (number / 2) else Nothing

checked :: Int -> Either String Int
checked number = if number < 0 then Left "negative" else Right (number + 1)

drain :: forall h. Int -> STArray h Int -> ST h Int
drain total stack = STArray.pop stack >>= case _ of
  Just top -> drain (total + top) stack
  Nothing -> pure total

drained :: Array Int -> Int
drained values = ST.run do
  stack <- STArray.thaw values
  drain 0 stack

halvesOf :: Array Int -> Maybe (Array Int)
halvesOf = traverse halved

checksOf :: Array Int -> Either String (Array Int)
checksOf = traverse checked

main :: { halvesOf :: Array Int -> Maybe (Array Int), checksOf :: Array Int -> Either String (Array Int), drained :: Array Int -> Int }
main = { halvesOf, checksOf, drained }
