module Main where

import Prelude

import Type.Proxy (Proxy(..))

data Box :: Row Type -> Type
data Box row = Box

class Labelled :: Type -> Type -> Constraint
class Labelled payload box | box -> payload where
  label :: Proxy box -> String

instance Labelled (Record (tag :: Int | row)) (Box row) where
  label _ = "box"

describe :: forall row. Labelled (Record (tag :: Int | row)) (Box row) => Box row -> String
describe _ = label (Proxy :: Proxy (Box row))

main :: Array String
main = [ describe Box ]
