module Main where

import Prelude

import Unsafe.Coerce (unsafeCoerce)

newtype Equal a b = Equal (forall f. f a -> f b)

refl :: forall a. Equal a a
refl = Equal identity

coerce :: forall a b. Equal a b -> a -> b
coerce _ = unsafeCoerce

symm :: forall a b. Equal a b -> Equal b a
symm _ = Equal unsafeCoerce

newtype Age = Age Int

data Value a
  = IntValue (Equal a Int) Int
  | AgeValue (Equal a Age) Age
  | StringValue (Equal a String) String
  | Pair (Value a) (Value a)

evaluate :: forall a. Value a -> a
evaluate (IntValue proof n) = coerce (symm proof) n
evaluate (AgeValue proof age) = coerce (symm proof) age
evaluate (StringValue proof s) = coerce (symm proof) s
evaluate (Pair left _) = evaluate left

main :: Array String
main =
  [ show (evaluate (Pair (IntValue refl 41) (IntValue refl 0)) + 1)
  , evaluate (Pair (StringValue refl "left") (StringValue refl "right"))
  ]
