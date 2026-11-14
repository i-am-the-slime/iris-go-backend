module Main where

import Prelude

import Data.Array (any, filter, foldl, length)
import Effect (Effect)
import Effect.Ref as Ref
import Effect.Unsafe (unsafePerformEffect)

-- Each pipeline's result is written before its counters are read, so the
-- counts say how often each callback ran: `filter` calls its predicate on
-- every element and the fused `map` only on the kept ones.
main
  :: { fused :: Int
     , predicateCalls :: Int
     , fusedMappingCalls :: Int
     , shared :: Int
     , sharedMappingCalls :: Int
     , earlyExit :: Boolean
     , earlyExitMappingCalls :: Int
     , keptLength :: Int
     }
main = unsafePerformEffect do
  predicates <- Ref.new 0
  mappings <- Ref.new 0
  fused <- Ref.new 0
  shared <- Ref.new 0
  earlyExit <- Ref.new false
  Ref.write (foldl (+) 0 (map (counted mappings (_ * 3)) (filter (counted predicates (_ > 2)) numbers))) fused
  predicateCalls <- Ref.read predicates
  fusedMappingCalls <- Ref.modify' (\calls -> { state: 0, value: calls }) mappings
  Ref.write (sharedIntermediate mappings) shared
  sharedMappingCalls <- Ref.modify' (\calls -> { state: 0, value: calls }) mappings
  Ref.write (any (_ > 20) (map (counted mappings (_ * 3)) numbers)) earlyExit
  earlyExitMappingCalls <- Ref.read mappings
  { fused: _, shared: _, earlyExit: _, predicateCalls, fusedMappingCalls, sharedMappingCalls, earlyExitMappingCalls, keptLength: _ }
    <$> Ref.read fused
    <*> Ref.read shared
    <*> Ref.read earlyExit
    <*> pure (length (filter (_ > 10) (map (_ * 3) numbers)))

numbers :: Array Int
numbers = [ 3, 1, 4, 1, 5, 9, 2, 6 ]

counted :: forall a b. Ref.Ref Int -> (a -> b) -> a -> b
counted counter f x = unsafePerformEffect do
  Ref.modify_ (_ + 1) counter
  pure (f x)

-- `tripled` is read twice, so it is built once and both readers share it.
sharedIntermediate :: Ref.Ref Int -> Int
sharedIntermediate mappings = do
  let tripled = map (counted mappings (_ * 3)) numbers
  foldl (+) 0 tripled + length tripled
