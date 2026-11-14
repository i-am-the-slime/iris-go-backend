module Bench.Exception.ExceptT where

import Prelude

import Bench.Harness (benchmark)
import Control.Monad.Except (Except, ExceptT, catchError, runExcept, runExceptT, throwError)
import Control.Monad.State (State, evalState, modify)
import Control.Monad.Trans.Class (lift)
import Data.Array ((..))
import Data.Either (either)
import Data.Foldable (foldl)
import Data.Traversable (traverse)
import Effect (Effect)

hypothesis :: String
hypothesis = "throwError and catchError in ExceptT over State in a hot loop: each bind goes through two layers of closures and Either allocation"

main :: Effect Unit
main = benchmark { size: 100000, workload }

workload :: Int -> String
workload n = do
  let viaExcept = foldl (\total i -> total + either (const 1) identity (runExcept (validate i))) 0 (1 .. n)
  let viaState = foldl (\total round -> total + either (const 0) identity (evalState (runExceptT (loop 0 round)) round)) 0 (1 .. (n / 2000))
  let traversed = either identity show (runExcept (traverse validate (map (\i -> i * 5 + 1) (1 .. 2000))))
  show viaExcept <> " " <> show viaState <> " " <> traversed
  where
  validate :: Int -> Except String Int
  validate i
    | i `mod` 5 == 0 = throwError ("bad " <> show i)
    | otherwise = pure (i `mod` 7)

  loop :: Int -> Int -> ExceptT String (State Int) Int
  loop i accumulated
    | i >= 2000 = pure accumulated
    | otherwise = do
        counted <- lift (modify (_ + 1))
        recovered <- catchError (if counted `mod` 4 == 0 then throwError "four" else pure counted) (\_ -> pure 0)
        loop (i + 1) ((accumulated + recovered) `mod` 1000003)
