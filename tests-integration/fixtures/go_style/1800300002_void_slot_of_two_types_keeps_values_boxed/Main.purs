module Main where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Void (Void)
import Effect (Effect)
import Effect.Console (log)
import Unsafe.Coerce (unsafeCoerce)

type Hooks = { onWord :: Maybe Void, onCount :: Maybe Void }

hooks :: Hooks
hooks = { onWord: Just (unsafeCoerce bracket), onCount: Just (unsafeCoerce double) }
  where
  bracket word = "<" <> word <> ">"
  double count = count * 2

wordHook :: Hooks -> String -> String
wordHook chosen word = case chosen.onWord of
  Just stored -> (unsafeCoerce stored :: String -> String) word
  Nothing -> word

countHook :: Hooks -> Int -> Int
countHook chosen count = case chosen.onCount of
  Just stored -> (unsafeCoerce stored :: Int -> Int) count
  Nothing -> count

repeatHooks :: Hooks -> String -> Int -> Int -> String
repeatHooks chosen word count rounds
  | rounds <= 0 = word <> " " <> show count
  | otherwise = repeatHooks chosen (wordHook chosen word) (countHook chosen count) (rounds - 1)

main :: Effect Unit
main = log (repeatHooks hooks "a" 1 3)
