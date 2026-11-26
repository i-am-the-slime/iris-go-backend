module Main where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Void (Void)
import Effect (Effect)
import Effect.Console (log)
import Unsafe.Coerce (unsafeCoerce)

type Hooks = { onWord :: Maybe Void, onLine :: Maybe Void }

hooks :: Hooks
hooks = { onWord: Just (unsafeCoerce bracket), onLine: Just (unsafeCoerce shout) }
  where
  bracket word = "<" <> word <> ">"
  shout line = line <> "!"

applyHook :: Maybe Void -> String -> String
applyHook hook text = case hook of
  Just stored -> (unsafeCoerce stored :: String -> String) text
  Nothing -> text

decorate :: Hooks -> Array String -> Int -> Array String
decorate chosen words rounds
  | rounds <= 0 = words
  | otherwise = decorate chosen (words <#> applyHook chosen.onWord) (rounds - 1)

main :: Effect Unit
main = do
  let decorated = decorate hooks [ "a", "b" ] 2
  log (applyHook hooks.onLine (Array.intercalate " " decorated))
  log (applyHook Nothing "untouched")
