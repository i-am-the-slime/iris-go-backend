module Main where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NonEmptyArray
import Data.Foldable (for_)
import Data.Maybe (fromJust)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Console (log)
import Partial.Unsafe (unsafePartial)
import Random.LCG (Seed, lcgNext, lcgPerturb, mkSeed, unSeed)
import Test.QuickCheck.Arbitrary (arbitrary)
import Test.QuickCheck.Gen (Gen, arrayOf, choose, chooseInt, elements, evalGen, frequency, resize, shuffle, uniform, vectorOf)

main :: Effect Unit
main = do
  for_ seeds \seed -> log ("lcg " <> show (unSeed seed) <> " " <> show (unSeed (lcgNext seed)) <> " " <> show (unSeed (lcgPerturb (perturbation seed) seed)))
  emit "int" (arbitrary :: Gen Int)
  emit "number" (arbitrary :: Gen Number)
  emit "uniform" uniform
  emit "string" (arbitrary :: Gen String)
  emit "char" (arbitrary :: Gen Char)
  emit "array" (arbitrary :: Gen (Array Int))
  emit "boolean" (arbitrary :: Gen Boolean)
  emit "chooseIntFull" (chooseInt bottom top)
  emit "chooseIntSmall" (chooseInt (-5) 17)
  emit "chooseIntReversed" (chooseInt 100 (-100))
  emit "choose" (choose (-1.5e10) 1.5e10)
  emit "elements" (elements letters)
  emit "frequency" (frequency (unsafePartial (fromJust (NonEmptyArray.fromArray [ Tuple 1.0 (pure "rare"), Tuple 7.5 (pure "common") ]))))
  emit "shuffle" (shuffle (Array.range 1 12))
  emit "bigString" (resize 200 (arbitrary :: Gen String))
  emit "nested" (arrayOf (arbitrary :: Gen (Array Number)))
  where
  seeds :: Array Seed
  seeds = Array.range 0 999 <#> \i -> mkSeed (i * 7919 - 3000000)

  perturbation :: Seed -> Int
  perturbation seed = unSeed seed * 31 + 2147483000

  letters = unsafePartial (fromJust (NonEmptyArray.fromArray [ "a", "b", "c", "d", "e" ]))

  emit :: forall a. Show a => String -> Gen a -> Effect Unit
  emit label generator = do
    let values = evalGen (vectorOf 1000 generator) { newSeed: mkSeed 12345, size: 10 }
    for_ (Array.mapWithIndex (\i value -> label <> " " <> show i <> " " <> show value) values) log
