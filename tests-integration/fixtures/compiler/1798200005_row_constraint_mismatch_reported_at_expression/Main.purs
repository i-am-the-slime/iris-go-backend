module Main where

import Prim.Row as Row

data Proxy :: forall k. k -> Type
data Proxy a = Proxy

data Variant :: Row Type -> Type
data Variant row = Variant

overOne
  :: forall label a b rest input output
   . Row.Cons label a rest input
  => Row.Cons label b rest output
  => Proxy label
  -> (a -> b)
  -> (Variant rest -> Variant output)
  -> Variant input
  -> Variant output
overOne _ _ _ _ = Variant

identity :: forall a. a -> a
identity a = a

variant :: Variant (a :: String, b :: Int)
variant = Variant

main :: Int
main = do
  let unused = 0
  let changed = overOne (Proxy :: Proxy "a") (\value -> value) identity variant
  unused
