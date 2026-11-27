module Main where

import Prim.RowList (RowList)
import Prim.RowList as RowList

data Proxy :: forall k. k -> Type
data Proxy a = Proxy

class Labels :: RowList Type -> Row Type -> Constraint
class Labels list row

instance Labels RowList.Nil ()

class Shape :: Type -> Constraint
class Shape a

instance Shape {}

instance Shape (Proxy ())

type Closed :: Row Type
type Closed = ()

class Named :: Type -> Constraint
class Named a

instance Named (Proxy Closed)

class Mirror :: Row Type -> Row Type -> Constraint
class Mirror left right | left -> right, right -> left

instance Mirror () ()

class Chosen :: Type -> Type -> Row Type -> Constraint
class Chosen key other row | key -> other, other -> key, other -> row

instance Chosen Int (Proxy ()) ()
