module Bench.Closure.FreeInterpreter where

import Prelude

import Bench.Harness (benchmark)
import Control.Monad.Free (Free, foldFree, liftF, resume)
import Control.Monad.State (State, evalState, get, put)
import Data.Either (Either(..))
import Data.List (List(..), (:))
import Effect (Effect)

hypothesis :: String
hypothesis = "a Free monad allocates a bind closure and a catenable queue node per step; V8's young generation makes them nearly free"

data Command next
  = Push Int next
  | Pop (Int -> next)
  | Add next

derive instance Functor Command

main :: Effect Unit
main = benchmark { size: 60000, workload }

workload :: Int -> String
workload n = show (stepByStep Nil (push 0 *> program n)) <> " " <> show (evalState (foldFree intoState (push 0 *> program n)) Nil)

program :: Int -> Free Command Int
program remaining
  | remaining <= 0 = pop
  | otherwise = do
      push remaining
      add
      top <- pop
      push (top `mod` 1000003)
      program (remaining - 1)

push :: Int -> Free Command Unit
push value = liftF (Push value unit)

pop :: Free Command Int
pop = liftF (Pop identity)

add :: Free Command Unit
add = liftF (Add unit)

stepByStep :: List Int -> Free Command Int -> Int
stepByStep stack current = case resume current of
  Right result -> result
  Left (Push value next) -> stepByStep (value : stack) next
  Left (Pop continue) -> case stack of
    top : rest -> stepByStep rest (continue top)
    Nil -> stepByStep Nil (continue 0)
  Left (Add next) -> case stack of
    first : second : rest -> stepByStep ((first + second) : rest) next
    _ -> stepByStep stack next

intoState :: Command ~> State (List Int)
intoState = case _ of
  Push value next -> do
    stack <- get
    put (value : stack)
    pure next
  Pop continue -> do
    stack <- get
    case stack of
      top : rest -> put rest $> continue top
      Nil -> pure (continue 0)
  Add next -> do
    stack <- get
    case stack of
      first : second : rest -> put ((first + second) : rest) $> next
      _ -> pure next
