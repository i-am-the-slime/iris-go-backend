module Main where

import Prelude

import Data.Either (Either(..))
import Data.Lazy as Lazy
import Data.Maybe (Maybe(..))
import Effect (Effect)

-- | Comparing with a known `Left Nothing` resolves the derived instance's second column, which
-- leaves alternatives that an earlier alternative already matches.
belowLeftNothing :: Either (Maybe Boolean) Int -> Boolean
belowLeftNothing value = value < Left Nothing

describe :: Maybe Int -> Int
describe = case _ of
  Nothing -> 1
  Nothing -> 2
  Just _ -> 3

recordField :: Either Int { b :: Ordering, v :: Int } -> Int
recordField = case _ of
  Right { v } -> v
  Right _ -> 2
  _ -> 3

main :: Effect Int
main = do
  let forced = Lazy.force (Lazy.defer \_ -> Left Nothing)
  let first = if belowLeftNothing forced then 1 else 0
  let second = if belowLeftNothing (Left (Just true)) then 10 else 0
  let third = if belowLeftNothing (Right 0) then 100 else 0
  pure (first + second + third + describe (Just 4) + recordField (Right { b: EQ, v: 1000 }))
