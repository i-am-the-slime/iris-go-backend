module Compat.Classes.Classes where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (class Foldable, foldMap, foldl, foldr, sum)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Coproduct (Coproduct, left, right, coproduct)
import Data.Functor.Product (Product, product)
import Data.Maybe (Maybe(..))
import Data.Monoid.Additive (Additive(..))
import Data.Newtype (unwrap)
import Data.Traversable (traverse)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Console (log)

class Container f elem | f -> elem where
  empty :: f
  insert :: elem -> f -> f
  toArray :: f -> Array elem

newtype IntBag = IntBag (Array Int)

instance Container IntBag Int where
  empty = IntBag []
  insert x (IntBag xs) = IntBag (Array.snoc xs x)
  toArray (IntBag xs) = xs

class Convert a b where
  convert :: a -> b

instance Convert Int String where
  convert = show

instance Convert Boolean Int where
  convert b = if b then 1 else 0

class Show a <= Pretty a where
  pretty :: a -> String

instance Pretty Int where
  pretty n = "#" <> show n

instance Pretty a => Pretty (Array a) where
  pretty xs = "[" <> Array.intercalate "; " (map pretty xs) <> "]"

describe :: forall a. Pretty a => a -> String
describe a = pretty a <> " (" <> show a <> ")"

class Monoid' a where
  mempty' :: a

instance Monoid' String where
  mempty' = ""

instance Monoid' b => Monoid' (a -> b) where
  mempty' = const mempty'

data Pair a = Pair a a

derive instance Functor Pair
instance Foldable Pair where
  foldr f z (Pair a b) = f a (f b z)
  foldl f z (Pair a b) = f (f z a) b
  foldMap f (Pair a b) = f a <> f b

main :: Effect Unit
main = do
  log (show (toArray (insert 3 (insert 2 (empty :: IntBag)))))
  log (convert (41 + 1) <> " " <> show (convert true + (convert false :: Int)))
  log (describe [ 1, 2 ])
  log ("<" <> (mempty' :: Int -> String) 5 <> ">")
  let composed = Compose [ Just 1, Nothing, Just 3 ]
  log (show (map (_ * 2) composed))
  log (show (sum composed))
  let both = product [ 1, 2 ] (Just 3)
  log (show (map (_ + 1) both))
  let either = [ left (Just 1), right [ 2, 3 ] ] :: Array (Coproduct Maybe Array Int)
  log (show (map (coproduct show show) either))
  log (show (foldMap Additive (Pair 4 5)) <> " " <> show (foldr (\a acc -> acc <> show a) "" (Pair 1 2)))
  log (show (unwrap (foldMap (\x -> Additive x) [ 1, 2, 3 ])))
  log (show ((mempty :: Int -> String) 1 <> "|" <> (show <> const "!") 2))
  log (show ({ a: "x", b: [ 1 ] } <> { a: "y", b: [ 2 ] }))
  log (show (mempty :: { a :: String, b :: Array Int }))
  log (show (traverse (\x -> if x > 0 then Right x else Left x) [ 1, 2, 3 ]))
  log (show (foldl (\acc (k /\ v) -> acc <> k <> show v) "" [ "a" /\ 1, "b" /\ 2 ]))
