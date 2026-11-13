module Data.Functor.Variant
  ( VariantF
  , inj
  , on
  , case_
  ) where

import Prelude

import Partial.Unsafe (unsafeCrashWith)
import Prim.Row as R
import Type.Proxy (Proxy)
import Data.Symbol (class IsSymbol, reflectSymbol)
import Unsafe.Coerce (unsafeCoerce)

newtype Mapper f = Mapper (forall a b. (a → b) → f a → f b)

newtype VariantFRep f a = VariantFRep
  { type ∷ String
  , value ∷ f a
  , map ∷ Mapper f
  }

data VariantF :: Row (Type -> Type) -> Type -> Type
data VariantF f a

instance functorVariantF ∷ Functor (VariantF r) where
  map f a =
    case coerceY a of
      VariantFRep v → coerceV $ VariantFRep
        { type: v.type
        , value: case v.map of Mapper m → m f v.value
        , map: v.map
        }
    where
    coerceY ∷ ∀ f a. VariantF r a → VariantFRep f a
    coerceY = unsafeCoerce

    coerceV ∷ ∀ f a. VariantFRep f a → VariantF r a
    coerceV = unsafeCoerce

inj
  ∷ ∀ sym f a r1 r2
  . R.Cons sym f r1 r2
  ⇒ IsSymbol sym
  ⇒ Functor f
  ⇒ Proxy sym
  → f a
  → VariantF r2 a
inj p value = coerceV $ VariantFRep { type: reflectSymbol p, value, map: Mapper map }
  where
  coerceV ∷ VariantFRep f a → VariantF r2 a
  coerceV = unsafeCoerce

on
  ∷ ∀ sym f a b r1 r2
  . R.Cons sym f r1 r2
  ⇒ IsSymbol sym
  ⇒ Proxy sym
  → (f a → b)
  → (VariantF r1 a → b)
  → VariantF r2 a
  → b
on p f g r =
  case coerceY r of
    VariantFRep v | v.type == reflectSymbol p → f v.value
    _ → g (coerceR r)
  where
  coerceY ∷ VariantF r2 a → VariantFRep f a
  coerceY = unsafeCoerce

  coerceR ∷ VariantF r2 a → VariantF r1 a
  coerceR = unsafeCoerce

case_ ∷ ∀ a b. VariantF () a → b
case_ r = unsafeCrashWith case unsafeCoerce r of
  VariantFRep v → "Data.Functor.Variant: pattern match failure [" <> v.type <> "]"
