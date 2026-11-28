module Main where

import Prelude

import Control.Monad.ST.Global (Global, toEffect)
import Control.Monad.ST (ST)
import Data.Array.ST (STArray)
import Data.Array.ST as STArray
import Data.Char (toCharCode)
import Data.Either (either)
import Data.Maybe (Maybe(..))
import Data.String.CodeUnits as String
import Data.String.Unsafe as Unsafe
import Effect (Effect)
import Effect.Console (log)
import Effect.Exception (message, try)

fillCodes :: STArray Global Int -> String -> Int -> ST Global Unit
fillCodes codes text index
  | index > String.length text = pure unit
  | otherwise = do
      _ <- STArray.push (toCharCode (Unsafe.charAt index text)) codes
      fillCodes codes text (index + 1)

popUntilLetter :: STArray Global Int -> Int -> ST Global Int
popUntilLetter stack total = STArray.pop stack >>= case _ of
  Just top -> popUntilLetter stack (total + toCharCode (Unsafe.charAt top "ab"))
  Nothing -> pure total

main :: Effect Unit
main = do
  codes <- toEffect STArray.new
  filled <- try (toEffect (fillCodes codes "hey" 0))
  log (either message (const "finished") filled)
  toEffect (STArray.unsafeFreeze codes) >>= show >>> log
  stack <- toEffect (STArray.unsafeThaw [ 5, 1, 0, 1 ])
  popped <- try (toEffect (popUntilLetter stack 0))
  log (either message show popped)
  toEffect (STArray.unsafeFreeze stack) >>= show >>> log
