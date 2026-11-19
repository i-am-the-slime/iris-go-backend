module Main where

import Prelude

import Data.Reflectable (class Reflectable, reflectType)
import Prim.Ordering (EQ, GT, LT)
import Type.Proxy (Proxy(..))

-- | `reflectType` of a type-level Ordering is the term-level constructor of the same name, also
-- through a `Reflectable` constraint.
reflected :: forall v. Reflectable v Ordering => Proxy v -> String
reflected proxy = show (reflectType proxy)

main :: Array String
main =
  [ show [ reflectType (Proxy :: _ LT), reflectType (Proxy :: _ EQ), reflectType (Proxy :: _ GT) ]
  , reflected (Proxy :: _ GT)
  , show (reflectType (Proxy :: _ LT) == LT)
  ]
