module Main where

import Prelude

import Data.Functor.Variant (Case, VariantF, VariantFRep(..), inj, mapper, overSome)
import Data.List (List(..), (:))
import Unsafe.Coerce (unsafeCoerce)

-- `Mapper`'s field is erased, because `VariantF`'s representation holds it at an erased functor.
-- `List`'s `Cons` holds the same field type in `maps`, and `overSome` moves its values into a
-- `VariantFRep` by coercion, so it stays erased there too.

data Box a = Box a

derive instance Functor Box

data Pair a = Pair a a

derive instance Functor Pair

swap :: forall a. Case a -> Case a
swap value = case (unsafeCoerce value :: Pair a) of
  Pair x y -> unsafeCoerce (Pair y x)

describe :: VariantF (first :: Box, second :: Pair) Int -> String
describe v = case (unsafeCoerce v :: VariantFRep Case Int) of
  VariantFRep rep
    | rep.type == "first" -> case (unsafeCoerce rep.value :: Box Int) of Box a -> "box " <> show a
    | otherwise -> case (unsafeCoerce rep.value :: Pair Int) of Pair a b -> "pair " <> show a <> " " <> show b

main :: Array String
main =
  [ describe (map (_ + 1) (inj "first" (Box 41)))
  , describe (map (_ * 2) (overSome "second" (mapper @Box : mapper @Pair : Nil) swap (inj "second" (Pair 1 2))))
  ]
