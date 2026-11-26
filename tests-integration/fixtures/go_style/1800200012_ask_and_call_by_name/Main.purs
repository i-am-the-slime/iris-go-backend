module Main where

import Prelude

import CallByName.Syntax (defer, lazy, (\\), (~))
import Control.Ask (class Ask, ask, provide)
import Data.Lazy (force)
import Effect (Effect)
import Effect.Console (log)

greeting :: Ask String => String
greeting = "hello " <> ask

shouted :: Ask String => Ask Int => String
shouted = greeting <> " x" <> show (ask :: Int)

twice :: (Unit -> Int) -> Int
twice thunk = thunk unit + thunk unit

main :: Effect Unit
main = do
  log (provide "mark" greeting)
  log (provide 3 (provide "both" shouted))
  log (show (defer (3 + 4) unit))
  log (show (force (lazy (6 * 7))))
  log (show (twice \\ (10 + 1)))
  log (show ((\later -> force later + 1) ~ 41))
