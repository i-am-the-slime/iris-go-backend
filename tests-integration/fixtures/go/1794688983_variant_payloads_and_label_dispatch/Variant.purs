module Data.Variant
  ( Variant
  , inj
  , on
  , onMatch
  , match
  , case_
  , default
  ) where

import Prelude

import Data.Symbol (class IsSymbol, reflectSymbol)
import Data.Variant.Internal (class VariantMatchCases, VariantRep(..), unsafeGet, unsafeHas)
import Partial.Unsafe (unsafeCrashWith)
import Prim.Row as R
import Prim.RowList as RL
import Type.Proxy (Proxy)
import Unsafe.Coerce (unsafeCoerce)

foreign import data Variant ∷ Row Type → Type

inj ∷ ∀ sym a r1 r2. R.Cons sym a r1 r2 ⇒ IsSymbol sym ⇒ Proxy sym → a → Variant r2
inj p value = coerceV $ VariantRep { type: reflectSymbol p, value }
  where
  coerceV ∷ VariantRep a → Variant r2
  coerceV = unsafeCoerce

on ∷ ∀ sym a b r1 r2. R.Cons sym a r1 r2 ⇒ IsSymbol sym ⇒ Proxy sym → (a → b) → (Variant r1 → b) → Variant r2 → b
on p f g r =
  case coerceV r of
    VariantRep v | v.type == reflectSymbol p → f v.value
    _ → g (coerceR r)
  where
  coerceV ∷ Variant r2 → VariantRep a
  coerceV = unsafeCoerce

  coerceR ∷ Variant r2 → Variant r1
  coerceR = unsafeCoerce

onMatch
  ∷ ∀ rl r r1 r2 r3 b
  . RL.RowToList r rl
  ⇒ VariantMatchCases rl r1 b
  ⇒ R.Union r1 r2 r3
  ⇒ Record r
  → (Variant r2 → b)
  → Variant r3
  → b
onMatch r k v =
  case coerceV v of
    VariantRep v' | unsafeHas v'.type r → unsafeGet v'.type r v'.value
    _ → k (coerceR v)
  where
  coerceV ∷ ∀ a. Variant r3 → VariantRep a
  coerceV = unsafeCoerce

  coerceR ∷ Variant r3 → Variant r2
  coerceR = unsafeCoerce

case_ ∷ ∀ a. Variant () → a
case_ r = unsafeCrashWith case unsafeCoerce r of
  VariantRep v → "Data.Variant: pattern match failure [" <> v.type <> "]"

match ∷ ∀ rl r r1 r2 b. RL.RowToList r rl ⇒ VariantMatchCases rl r1 b ⇒ R.Union r1 () r2 ⇒ Record r → Variant r2 → b
match r = case_ # onMatch r

default ∷ ∀ a r. a → Variant r → a
default a _ = a
