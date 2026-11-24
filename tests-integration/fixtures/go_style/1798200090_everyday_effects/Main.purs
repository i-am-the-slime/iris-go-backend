module Fun.Effects where

import Prelude

import Control.Monad.Rec.Class (Step(..), tailRec, tailRecM, tailRecM2, forever)
import Control.Monad.ST (ST)
import Control.Monad.ST as ST
import Control.Monad.ST.Ref as STRef
import Data.Array.ST as STArray
import Data.Array (range, length)
import Data.Either (Either(..), either)
import Data.Tuple.Nested ((/\))
import Data.Maybe (Maybe(..))
import Data.Foldable (for_)
import Effect (Effect, whileE, forE, foreachE)
import Effect.Console (log)
import Effect.Exception (catchException, error, message, throwException, try, throw)
import Effect.Ref as Ref
import Effect.Uncurried (EffectFn2, mkEffectFn2, runEffectFn2, EffectFn1, mkEffectFn1, runEffectFn1)
import Data.Function.Uncurried (Fn3, mkFn3, runFn3)

sumST :: Int -> Int
sumST limit = ST.run do
  total <- STRef.new 0
  ST.for 0 limit \i -> STRef.modify (_ + i) total
  STRef.read total

sumSTWhile :: Int -> Int
sumSTWhile limit = ST.run do
  total <- STRef.new 0
  counter <- STRef.new 0
  ST.while (STRef.read counter <#> (_ < limit)) do
    i <- STRef.read counter
    _ <- STRef.modify (_ + i) total
    void (STRef.modify (_ + 1) counter)
  STRef.read total

squaresST :: Int -> Array Int
squaresST n = STArray.run do
  squares <- STArray.new
  ST.for 0 n \i -> void (STArray.push (i * i) squares)
  _ <- STArray.modify 0 (_ + 100) squares
  pure squares

reverseInPlace :: Array Int -> Array Int
reverseInPlace input = STArray.run do
  arr <- STArray.thaw input
  let size = length input
  ST.for 0 (size / 2) \i -> do
    left <- STArray.peek i arr
    right <- STArray.peek (size - 1 - i) arr
    case left, right of
      Just l, Just r -> do
        _ <- STArray.poke i r arr
        void (STArray.poke (size - 1 - i) l arr)
      _, _ -> pure unit
  pure arr

countDown :: Int -> Effect Int
countDown = tailRecM step
  where
  step n
    | n <= 0 = pure (Done 0)
    | otherwise = pure (Loop (n - 1))

sumTo :: Int -> Effect Int
sumTo limit = tailRecM2 step 0 0
  where
  step acc i
    | i > limit = pure (Done acc)
    | otherwise = pure (Loop { a: acc + i, b: i + 1 })

collatzSteps :: Int -> Int
collatzSteps = tailRec step <<< (_ /\ 0)
  where
  step (n /\ steps)
    | n == 1 = Done steps
    | n `mod` 2 == 0 = Loop ((n / 2) /\ (steps + 1))
    | otherwise = Loop ((3 * n + 1) /\ (steps + 1))

sumMaybeRec :: Int -> Maybe Int
sumMaybeRec limit = tailRecM go (0 /\ 0)
  where
  go (acc /\ i)
    | i > limit = Just (Done acc)
    | otherwise = Just (Loop ((acc + i) /\ (i + 1)))

sumEitherRec :: Int -> Either String Int
sumEitherRec limit = tailRecM go (0 /\ 0)
  where
  go (acc /\ i)
    | i > limit = Right (Done acc)
    | i == -1 = Left "impossible"
    | otherwise = Right (Loop ((acc + i) /\ (i + 1)))

addThree :: Fn3 Int Int Int Int
addThree = mkFn3 \a b c -> a + b + c

logBoth :: EffectFn2 String Int Unit
logBoth = mkEffectFn2 \label n -> log (label <> ": " <> show n)

doubleEffect :: EffectFn1 Int Int
doubleEffect = mkEffectFn1 \n -> pure (n * 2)

safeDivide :: Int -> Int -> Effect Int
safeDivide _ 0 = throwException (error "divide by zero")
safeDivide a b = pure (a / b)

main :: Effect Unit
main = do
  log $ show (sumST 1000000)
  log $ show (sumSTWhile 1000000)
  log $ show (squaresST 6)
  log $ show (reverseInPlace [ 1, 2, 3, 4, 5 ])
  countDown 1000000 >>= show >>> log
  sumTo 1000000 >>= show >>> log
  log $ show (collatzSteps 27)
  log $ show (sumMaybeRec 1000000)
  log $ show (sumEitherRec 1000000)
  counter <- Ref.new 0
  whileE (Ref.read counter <#> (_ < 1000000)) (Ref.modify_ (_ + 1) counter)
  Ref.read counter >>= show >>> log
  accumulated <- Ref.new 0
  forE 0 1000000 \i -> Ref.modify_ (_ + i) accumulated
  Ref.read accumulated >>= show >>> log
  foreachE (range 1 5) \i -> Ref.modify_ (_ * 2) accumulated # when (i > 3)
  Ref.read accumulated >>= show >>> log
  newValue <- Ref.modify (_ - 1) accumulated
  log $ show newValue
  old <- Ref.modify' (\s -> { state: s + 1, value: s }) accumulated
  log $ show old
  log $ show (runFn3 addThree 1 2 3)
  runEffectFn2 logBoth "label" 42
  runEffectFn1 doubleEffect 21 >>= show >>> log
  divided <- try (safeDivide 10 0)
  log $ either message show divided
  divided2 <- try (safeDivide 10 3)
  log $ either message show divided2
  recovered <- catchException (\err -> pure ("caught " <> message err)) (throw "boom" <#> \(_ :: Unit) -> "unreachable")
  log recovered
  nested <- try (catchException (\err -> throw ("rethrown " <> message err)) (throw "inner"))
  log $ either message (\(_ :: Unit) -> "no") nested
  attempt <- try (forE 0 10 \i -> when (i == 5) (throw ("at " <> show i)))
  log $ either message show attempt
  escaped <- try do
    loopRef <- Ref.new 0
    forever do
      n <- Ref.modify (_ + 1) loopRef
      when (n >= 100000) (throw ("stopped at " <> show n))
  log $ either message (const "never") escaped
  for_ [ 1, 2 ] \i -> log (show i)
  where
  _unused = Left 1 :: Either Int Int
