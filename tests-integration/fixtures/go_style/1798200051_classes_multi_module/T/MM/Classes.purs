module T.MM.Classes where

import Prelude

import Data.Foldable (foldl)
import Data.Tuple (fst)
import Data.Tuple.Nested ((/\))
import Data.Symbol (class IsSymbol, reflectSymbol)
import Type.Proxy (Proxy(..))

class Pretty a where
  pretty :: a -> String

class Pretty a <= Summary a where
  summary :: a -> String
  weight :: a -> Int

class Tagged :: Symbol -> Type -> Constraint
class IsSymbol tag <= Tagged tag a | a -> tag

tagOf :: forall @a tag. Tagged tag a => String
tagOf = reflectSymbol (Proxy @tag)

heaviest :: forall a. Summary a => Array a -> String
heaviest items = items # foldl pickHeavier ("none" /\ bottom) # fst
  where
  pickHeavier (best /\ bestWeight) item
    | weight item > bestWeight = summary item /\ weight item
    | otherwise = best /\ bestWeight

instance Pretty Int where pretty = show
instance Summary Int where
  summary n = "int " <> pretty n
  weight = identity
instance Tagged "int" Int
