module Data.Variant.Internal
  ( VariantRep(..)
  , class VariantMatchCases
  , module Exports
  ) where

import Prim.Row as R
import Prim.RowList as RL
import Record.Unsafe (unsafeGet, unsafeHas) as Exports
import Type.Equality (class TypeEquals)

newtype VariantRep a = VariantRep
  { type ∷ String
  , value ∷ a
  }

class VariantMatchCases :: RL.RowList Type -> Row Type -> Type -> Constraint
class VariantMatchCases rl vo b | rl → vo b

instance variantMatchCons
  ∷ ( VariantMatchCases rl vo' b
    , R.Cons sym a vo' vo
    , TypeEquals k (a → b)
    )
  ⇒ VariantMatchCases (RL.Cons sym k rl) vo b

instance variantMatchNil
  ∷ VariantMatchCases RL.Nil () b
