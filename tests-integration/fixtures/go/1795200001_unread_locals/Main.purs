module Main where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Int as Int
import Data.Maybe (Maybe(..), fromMaybe)
import Effect (Effect)
import Effect.Ref as Ref

-- | The record scrutinee binds `items`, which the alternative never reads.
label :: Either Int Int -> Int
label (Right (-1)) = case { items: Array.sort [ 'b', 'a' ] } of
  { items } -> 2
label _ = 1

-- | A branching value that only an unread binding holds.
chosen :: Maybe Int -> Int
chosen candidate = fromMaybe 0 (Array.index [ 10, 20 ] (fromMaybe 1 candidate))

main :: Effect Int
main = do
  truncated <- Ref.new (Int.trunc 0.5)
  value <- Ref.read truncated
  items <- Ref.new (fromMaybe [] (Array.deleteAt 0 ([] :: Array Int)))
  counter <- Ref.new 0
  modified <- Ref.modify' (\count -> { state: count + 1, value: chosen (Just count) }) counter
  branch <- pure (chosen Nothing)
  total <- Ref.read counter
  pure (total * 10 + label (Right (-1)))
