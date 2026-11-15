module Main where

import Prim.Row as R
import Prim.RowList as RL

class T (f :: Type -> Type)

data V (r :: Row (Type -> Type)) a = V

class TRL (rl :: RL.RowList (Type -> Type)) (r :: Row (Type -> Type))

instance (RL.RowToList r rl, TRL rl r) => T (V r)

-- Mirrors variant's VariantFTraverseCases: the cases' RowList determines `ri`.
class Cases (rl :: RL.RowList Type) (ri :: Row (Type -> Type)) | rl -> ri

instance Cases RL.Nil ()

-- Mirrors variant's `TypeEquals k (f a -> m (g b))`: the handler's type determines `f`.
class Handler k (f :: Type -> Type) | k -> f

instance Handler (f a -> f b) f

instance (R.Cons sym f ri' ri, Cases rl ri', Handler k f) => Cases (RL.Cons sym k rl) ri

data P (r :: Row (Type -> Type)) = P

data Id a = Id a

elim :: forall cases casesrl affected unaffected all.
  RL.RowToList cases casesrl =>
  Cases casesrl affected =>
  R.Union affected unaffected all =>
  T (V unaffected) =>
  Record cases -> P all -> Int
elim _ _ = 0

test :: forall r. T (V r) => P (x :: Id | r) -> Int
test = elim { x: \(Id n) -> Id n }

