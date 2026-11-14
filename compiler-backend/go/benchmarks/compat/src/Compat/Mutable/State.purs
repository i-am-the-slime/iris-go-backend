module Compat.Mutable.State where

import Prelude

import Control.Monad.ST (ST, run, for, while)
import Control.Monad.ST.Ref as STRef
import Data.Array.ST as STArray
import Data.Array.ST.Iterator as Iterator
import Data.Array as Array
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Console (log)
import Effect.Ref as Ref

sieve :: Int -> Array Int
sieve limit = run do
  flags <- STArray.unsafeThaw (Array.replicate (limit + 1) true)
  for 2 (limit + 1) \i -> do
    isPrime <- STArray.peek i flags
    when (isPrime == Just true) do
      multiple <- STRef.new (i * i)
      while ((_ <= limit) <$> STRef.read multiple) do
        m <- STRef.read multiple
        _ <- STArray.poke m false flags
        void (STRef.modify (_ + i) multiple)
  frozen <- STArray.unsafeFreeze flags
  pure (Array.filter (\i -> i >= 2 && Array.index frozen i == Just true) (Array.range 0 limit))

sumIterator :: Array Int -> Int
sumIterator xs = run do
  total <- STRef.new 0
  iterator <- Iterator.iterator (Array.index xs)
  Iterator.iterate iterator \x -> void (STRef.modify (_ + x) total)
  STRef.read total

sortInPlace :: Array Int -> Array Int
sortInPlace xs = STArray.run do
  array <- STArray.thaw xs
  _ <- STArray.sortBy (flip compare) array
  _ <- STArray.push 0 array
  pure array

type Counter = { increment :: Effect Unit, current :: Effect Int }

newtype Widget = Widget { name :: String, clicks :: Ref.Ref Int, onClick :: Effect Unit }

makeCounter :: Effect Counter
makeCounter = do
  ref <- Ref.new 0
  pure { increment: Ref.modify_ (_ + 1) ref, current: Ref.read ref }

makeWidget :: String -> Effect Widget
makeWidget name = do
  clicks <- Ref.new 0
  pure (Widget { name, clicks, onClick: Ref.modify_ (_ + 10) clicks })

main :: Effect Unit
main = do
  log (show (sieve 50))
  log (show (sumIterator [ 1, 2, 3, 4, 5 ]))
  log (show (sortInPlace [ 3, 1, 2 ]))
  counter <- makeCounter
  for_ (Array.range 1 5) \_ -> counter.increment
  n <- counter.current
  log (show n)
  widgets <- traverse' makeWidget [ "ok", "cancel" ]
  for_ widgets \(Widget w) -> w.onClick *> w.onClick
  for_ widgets \(Widget w) -> do
    clicks <- Ref.read w.clicks
    log (w.name <> " " <> show clicks)
  where
  traverse' f = Array.foldM (\acc x -> f x <#> \w -> Array.snoc acc w) []
