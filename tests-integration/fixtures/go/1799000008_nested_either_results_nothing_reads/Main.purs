module Main where

import Prelude

import Data.Either (Either(..))
import Data.Int as Int
import Data.Maybe (Maybe(..))
import Data.Traversable (for_)
import Effect (Effect)
import Journal (log)

parse :: String -> Either String Int
parse text = case Int.fromString text of
  Just n -> Right n
  Nothing -> Left ("not a number: " <> text)

readSide :: Int -> Either String (Either Int Int)
readSide n
  | n > 1000 = readSide (n - 1000)
  | n < 0 = Left "negative"
  | n `mod` 2 == 0 = Right (Left (n / 2))
  | otherwise = Right (Right n)

readText :: String -> Either String (Either Int Int)
readText text = parse text >>= readSide

shouldRead :: Int -> Effect Unit
shouldRead = readSide >>> case _ of
  Left failure -> log ("failed: " <> failure)
  Right (_ :: Either Int Int) -> pure unit

shouldReadText :: String -> Effect Unit
shouldReadText = readText >>> case _ of
  Left failure -> log ("failed: " <> failure)
  Right (_ :: Either Int Int) -> pure unit

main :: Effect Unit
main = for_ [ "4", "2001", "-3", "x" ] \text -> do
  shouldReadText text
  for_ (Int.fromString text) shouldRead
