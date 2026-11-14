module Compat.Laziness.Lazy where

import Prelude

import Control.Lazy (fix, defer)
import Data.Lazy (Lazy, force)
import Data.Lazy as Lazy
import Data.List.Lazy as LazyList
import Data.List.Lazy.Types as LazyTypes
import Effect (Effect)
import Effect.Console (log)
import Effect.Ref as Ref
import Effect.Unsafe (unsafePerformEffect)

ones :: LazyList.List Int
ones = fix \xs -> LazyList.cons 1 xs

fibonacci :: LazyList.List Int
fibonacci = fix \fibs -> LazyList.cons 0 (LazyList.cons 1 (LazyList.zipWith (+) fibs (LazyList.drop 1 fibs)))

isEven :: Int -> Boolean
isEven = defer \_ -> \n -> if n == 0 then true else isOdd (n - 1)

isOdd :: Int -> Boolean
isOdd = defer \_ -> \n -> if n == 0 then false else isEven (n - 1)

data Rose = Rose Int (Lazy (Array Rose))

knot :: Lazy { left :: Lazy Int, right :: Lazy Int }
knot = fix \self -> Lazy.defer \_ ->
  { left: Lazy.defer \_ -> 1
  , right: Lazy.defer \_ -> force (force self).left + 41
  }

counter :: Ref.Ref Int
counter = unsafePerformEffect (Ref.new 0)

memoised :: Lazy Int
memoised = Lazy.defer \_ -> unsafePerformEffect do
  Ref.modify_ (_ + 1) counter
  pure 7

main :: Effect Unit
main = do
  log (show (LazyList.take 5 ones))
  log (show (LazyList.take 12 fibonacci))
  log (show (isEven 10) <> " " <> show (isOdd 7))
  log (show (force (force knot).right))
  log (show (force memoised + force memoised))
  evaluations <- Ref.read counter
  log (show evaluations)
  log (show (LazyList.take 3 (LazyList.iterate (_ * 2) 1)))
  log (show (map (_ * 10) (Lazy.defer \_ -> 4)))
  log (show (LazyList.length (LazyList.filter isEven (LazyList.range 1 100))))
  let tree = Rose 1 (Lazy.defer \_ -> [ Rose 2 (pure []), Rose 3 (pure []) ])
  log (case tree of Rose root children -> show root <> " " <> show (map (\(Rose n _) -> n) (force children)))
  _ <- pure LazyTypes.nil
  pure unit
