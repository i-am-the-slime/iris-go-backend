module Data.Functor.Variant
  ( VariantF
  , VariantFRep(..)
  , Case
  , Mapper(..)
  , inj
  , mapper
  , overSome
  , module Prelude
  ) where

import Prelude

import Data.List (List(..), (:))
import Unsafe.Coerce (unsafeCoerce)

newtype Mapper f = Mapper (forall a b. (a -> b) -> f a -> f b)

newtype VariantFRep f a = VariantFRep { type :: String, value :: f a, map :: Mapper f }

data Case :: Type -> Type
data Case a

data VariantF :: Row (Type -> Type) -> Type -> Type
data VariantF r a

instance Functor (VariantF r) where
  map f a = case coerceY a of
    VariantFRep v -> coerceV (VariantFRep { type: v.type, value: case v.map of Mapper m -> m f v.value, map: v.map })
    where
    coerceY :: forall g x. VariantF r x -> VariantFRep g x
    coerceY = unsafeCoerce

    coerceV :: forall g x. VariantFRep g x -> VariantF r x
    coerceV = unsafeCoerce

inj :: forall r f a. Functor f => String -> f a -> VariantF r a
inj tag value = unsafeCoerce (VariantFRep { type: tag, value, map: Mapper map })

-- A label's mapper as `variantFMaps` lists it, coerced to the case functor.
mapper :: forall @f. Functor f => Mapper Case
mapper = coerceMap (Mapper map :: Mapper f)
  where
  coerceMap :: Mapper f -> Mapper Case
  coerceMap = unsafeCoerce

lookup :: forall a. String -> List String -> List a -> a
lookup tag (Cons t ts) (Cons m ms) = if t == tag then m else lookup tag ts ms
lookup tag _ _ = lookup tag Nil Nil

overSome
  :: forall r a
   . String
  -> List (Mapper Case)
  -> (Case a -> Case a)
  -> VariantF r a
  -> VariantF r a
overSome tag maps f v = case coerceV v of
  VariantFRep v' | v'.type == tag ->
    coerceV' (VariantFRep { type: v'.type, map: lookup v'.type ("first" : "second" : Nil) maps, value: f v'.value })
  _ -> v
  where
  coerceV :: forall h. VariantF r a -> VariantFRep h a
  coerceV = unsafeCoerce

  coerceV' :: forall h. VariantFRep h a -> VariantF r a
  coerceV' = unsafeCoerce
