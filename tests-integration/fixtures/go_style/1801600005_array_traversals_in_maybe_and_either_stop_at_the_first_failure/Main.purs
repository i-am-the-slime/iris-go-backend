module Main where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldl)
import Data.Maybe (Maybe(..))
import Data.Traversable (sequence, traverse)
import Partial.Unsafe (unsafeCrashWith)
import Effect (Effect)
import Effect.Console (log)

doubledWhenNatural :: Int -> Maybe Int
doubledWhenNatural number = if number >= 0 then Just (number * 2) else Nothing

validated :: Int -> Either String Int
validated number
  | number < 0 = Left ("negative " <> show number)
  | otherwise = Right (number + 1)

evensKept :: Array Int -> Maybe (Array Int)
evensKept = foldl keep (Just [])
  where
  keep (Just kept) number | number `mod` 2 == 0 = Just (Array.snoc kept number)
  keep (Just kept) _ = Just kept
  keep Nothing _ = Nothing

appendedAfter :: Array Int -> Array Int -> Maybe (Array Int)
appendedAfter start = foldl step (Just start)
  where
  step (Just kept) number = if number > 100 then Nothing else Just (Array.snoc kept number)
  step Nothing _ = Nothing

startingFrom :: Maybe (Array Int) -> Array Int -> Maybe (Array Int)
startingFrom = foldl step
  where
  step (Just kept) number
    | number == 99 = unsafeCrashWith "a step ran on an absorbed accumulator"
    | number > 100 = Nothing
    | otherwise = Just (Array.snoc kept number)
  step Nothing _ = Nothing

main :: Effect Unit
main = do
  log (show (traverse doubledWhenNatural [ 1, 2, 3 ]))
  log (show (traverse doubledWhenNatural [ 1, -2, 3 ]))
  log (show (traverse doubledWhenNatural ([] :: Array Int)))
  log (show (traverse doubledWhenNatural (Array.range 0 9)))
  log (show (sequence [ Just 1, Just 2, Just 3 ]))
  log (show (sequence [ Just 1, Nothing, Just 3 ]))
  log (show (traverse validated [ 4, 5, 6 ]))
  log (show (traverse validated [ 4, -5, -6 ]))
  log (show (sequence [ Right 1, Left "first", Left "second" ] :: Either String (Array Int)))
  log (show (evensKept [ 1, 2, 3, 4, 5, 6 ]))
  log (show (appendedAfter [ 7, 8 ] [ 1, 2, 3 ]))
  log (show (appendedAfter [ 7, 8 ] [ 1, 200, 3 ]))
  let source = [ 10, 20 ]
  log (show (appendedAfter source [ 30 ]))
  log (show (appendedAfter source [ 40 ]))
  log (show source)
  log (show (startingFrom Nothing [ 99, 1 ]))
  log (show (startingFrom (Just [ 5 ]) [ 6, 7 ]))
  log (show (startingFrom (Just [ 5 ]) [ 6, 200, 99 ]))
