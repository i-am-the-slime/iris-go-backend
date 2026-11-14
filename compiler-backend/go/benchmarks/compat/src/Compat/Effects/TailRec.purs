module Compat.Effects.TailRec where

import Prelude

import Control.Monad.Rec.Class (Step(..), tailRec, tailRecM, forever)
import Control.Monad.State (StateT, evalStateT, get, put, runStateT)
import Control.Monad.Except (ExceptT, runExceptT, throwError)

import Data.Identity (Identity)
import Data.Newtype (unwrap)
import Effect (Effect)
import Effect.Console (log)
import Effect.Ref as Ref

collatz :: Int -> Int
collatz = tailRec step <<< { n: _, steps: 0 }
  where
  step { n, steps }
    | n == 1 = Done steps
    | n `mod` 2 == 0 = Loop { n: n / 2, steps: steps + 1 }
    | otherwise = Loop { n: 3 * n + 1, steps: steps + 1 }

sumTo :: Int -> Effect Int
sumTo limit = tailRecM go { i: 0, total: 0 }
  where
  go { i, total }
    | i > limit = pure (Done total)
    | otherwise = pure (Loop { i: i + 1, total: total + i })

countDown :: StateT Int Identity String
countDown = tailRecM go unit
  where
  go _ = do
    n <- get
    if n <= 0 then pure (Done "liftoff") else put (n - 1) $> Loop unit

untilFailure :: ExceptT String Effect Unit
untilFailure = do
  counter <- pure 0
  forever (throwError ("stopped after " <> show counter))

main :: Effect Unit
main = do
  log (show (collatz 27))
  total <- sumTo 100000
  log (show total)
  log (unwrap (evalStateT countDown 100000))
  log (show (unwrap (runStateT countDown 3)))
  result <- runExceptT untilFailure
  log (show result)
  ref <- Ref.new 0
  final <- tailRecM (\n -> if n >= 50000 then pure (Done n) else Ref.modify_ (_ + 2) ref $> Loop (n + 1)) 0
  seen <- Ref.read ref
  log (show final <> " " <> show seen)
