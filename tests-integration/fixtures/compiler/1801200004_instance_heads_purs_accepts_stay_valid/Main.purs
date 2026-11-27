module Main where

import Prim.RowList (RowList)
import Prim.RowList as RowList

data Proxy :: forall k. k -> Type
data Proxy a = Proxy

class Labels :: RowList Type -> Row Type -> Constraint
class Labels list row | list -> row

instance Labels RowList.Nil ()

instance Labels (RowList.Cons label Int tail) (label :: Int | row)

class Shape :: Type -> Constraint
class Shape a

instance Shape (Proxy ( | row ))

instance Shape (Proxy "name")

instance Shape (Proxy 42)

instance Shape (Int -> Proxy Int)

class Recorded :: Type -> Type -> Constraint
class Recorded key record | key -> record

instance Recorded Int { name :: Int }

class Chosen :: Type -> Type -> Row Type -> Constraint
class Chosen key other row | key -> other, other -> key, other -> row

instance Chosen Int (Proxy Int) (name :: Int)
