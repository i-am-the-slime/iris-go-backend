module Compat.Effects.FreeCofree where

import Prelude

import Control.Comonad.Cofree (Cofree, deferCofree, head, tail)
import Control.Monad.Free (Free, liftF, foldFree, resume, runFree)
import Control.Monad.State (State, evalState, get, put, modify_)
import Data.Either (Either(..))
import Data.Identity (Identity(..))
import Data.Newtype (unwrap)
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Effect.Console (log)

data CounterF a = Increment Int a | Read (Int -> a)

derive instance Functor CounterF

increment :: Int -> Free CounterF Unit
increment n = liftF (Increment n unit)

read :: Free CounterF Int
read = liftF (Read identity)

script :: Free CounterF String
script = do
  increment 3
  a <- read
  increment (a * 2)
  b <- read
  pure ("a=" <> show a <> " b=" <> show b)

newtype CoCounter a = CoCounter { increment :: Int -> a, read :: Int /\ a }

derive instance Functor CoCounter

counter :: Int -> Cofree CoCounter Int
counter n = deferCofree \_ -> n /\ CoCounter { increment: \k -> counter (n + k), read: n /\ counter n }

pair :: forall a. Cofree CoCounter Int -> Free CounterF a -> a
pair machine program = case resume program of
  Right a -> a
  Left (Increment n next) -> case tail machine of CoCounter c -> pair (c.increment n) next
  Left (Read continue) -> case tail machine of
    CoCounter c -> case c.read of
      value /\ machine' -> pair machine' (continue value)

toState :: CounterF ~> State Int
toState (Increment n next) = modify_ (_ + n) $> next
toState (Read continue) = continue <$> get

main :: Effect Unit
main = do
  log (pair (counter 1) script)
  log (evalState (foldFree toState script) 10)
  log (show (head (counter 7)))
  log (runFree (\f -> case f of
    Increment _ next -> next
    Read continue -> continue 100) script)
  log (unwrap (Identity "identity"))
  log (evalState (put 3 *> get <#> show) 0)
