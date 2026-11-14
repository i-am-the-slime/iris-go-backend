module Compat.Generics.Generic where

import Prelude

import Data.Array as Array
import Data.Bounded.Generic (genericBottom, genericTop)
import Data.Enum (class BoundedEnum, class Enum, enumFromTo, fromEnum, succ, pred, toEnum, upFromIncluding)
import Data.Enum.Generic (genericCardinality, genericFromEnum, genericPred, genericSucc, genericToEnum)
import Data.Eq.Generic (genericEq)
import Data.Generic.Rep (class Generic, Argument(..), Constructor(..), NoArguments(..), NoConstructors, Product(..), Sum(..), from, to)
import Data.Maybe (Maybe(..))
import Data.Ord.Generic (genericCompare)
import Data.Show.Generic (genericShow)
import Data.Symbol (class IsSymbol, reflectSymbol)
import Effect (Effect)
import Effect.Console (log)
import Type.Proxy (Proxy(..))

data Suit = Clubs | Diamonds | Hearts | Spades

derive instance Generic Suit _
instance Eq Suit where
  eq = genericEq
instance Ord Suit where
  compare = genericCompare
instance Show Suit where
  show = genericShow
instance Bounded Suit where
  bottom = genericBottom
  top = genericTop
instance Enum Suit where
  succ = genericSucc
  pred = genericPred
instance BoundedEnum Suit where
  cardinality = genericCardinality
  toEnum = genericToEnum
  fromEnum = genericFromEnum

data Tree a = Leaf | Node (Tree a) a (Tree a)

derive instance Generic (Tree a) _
instance Show a => Show (Tree a) where
  show tree = genericShow tree

data Card = Card Suit Int | Joker

derive instance Generic Card _

class ConstructorNames :: Type -> Constraint
class ConstructorNames rep where
  constructorNames :: Proxy rep -> Array String

instance ConstructorNames NoConstructors where
  constructorNames _ = []

instance IsSymbol name => ConstructorNames (Constructor name arguments) where
  constructorNames _ = [ reflectSymbol (Proxy @name) ]

instance (ConstructorNames left, ConstructorNames right) => ConstructorNames (Sum left right) where
  constructorNames _ = constructorNames (Proxy @left) <> constructorNames (Proxy @right)

names :: forall @a rep. Generic a rep => ConstructorNames rep => Array String
names = constructorNames (Proxy @rep)

class CountFields rep where
  countFields :: rep -> Int

instance CountFields NoArguments where
  countFields _ = 0

instance CountFields (Argument a) where
  countFields _ = 1

instance (CountFields left, CountFields right) => CountFields (Product left right) where
  countFields (Product left right) = countFields left + countFields right

instance CountFields arguments => CountFields (Constructor name arguments) where
  countFields (Constructor arguments) = countFields arguments

instance (CountFields left, CountFields right) => CountFields (Sum left right) where
  countFields (Inl left) = countFields left
  countFields (Inr right) = countFields right

fields :: forall a rep. Generic a rep => CountFields rep => a -> Int
fields = countFields <<< from

main :: Effect Unit
main = do
  log (show (enumFromTo bottom top :: Array Suit))
  log (show (succ Hearts) <> " " <> show (pred Clubs) <> " " <> show (fromEnum Spades) <> " " <> show (toEnum 1 :: Maybe Suit))
  log (show (upFromIncluding Diamonds :: Array Suit))
  log (show (compare Hearts Diamonds) <> " " <> show (Clubs == Clubs))
  log (show (Node (Node Leaf 1 Leaf) 2 Leaf))
  log (show (names @Card) <> " " <> show (names @Suit))
  log (show (map fields [ Card Hearts 3, Joker ]))
  log (show (Array.length (names @(Tree Int))))
  log (show (to (from Spades) :: Suit))
  _ <- pure NoArguments
  pure unit
