module Main where

import Prelude

import Control.Monad.Rec.Class (Step(..), tailRec)
import Effect (Effect)
import Effect.Ref as Ref
import Effect.Unsafe (unsafePerformEffect)

bump :: Ref.Ref Int -> Int -> Int -> Int
bump count amount value = unsafePerformEffect (Ref.modify_ (_ + amount) count *> pure value)

countdown :: Ref.Ref Int -> Int -> Int -> Int
countdown count n acc = if n <= 0 then acc else countdown count (n - 1) (bump count 10 acc)

iterate :: (Int -> Int) -> Int -> Int -> Int
iterate f n x = if n <= 0 then x else iterate f (n - 1) (f x)

ignore :: Int -> Int
ignore _ = 0

-- | An argument the function ignores still runs its effects, as JavaScript evaluates it: through
-- a `tailRec` loop, a recursive function, or a function passed to a recursive one. The count is 111.
main :: Effect Int
main = do
  count <- Ref.new 0
  let looped = ignore (tailRec (\st -> if st.i >= 1 then Done st.acc else Loop { acc: bump count 1 st.acc, i: st.i + 1 }) { acc: 3, i: 0 })
  let counted = ignore (countdown count 1 3)
  let iterated = ignore (iterate (bump count 100) 1 3)
  total <- Ref.read count
  pure (looped + counted + iterated + total)
