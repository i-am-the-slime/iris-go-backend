module T.MM.Types where

import Prelude

import Data.Array as Array
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import T.MM.Classes (class Pretty, class Summary, class Tagged, pretty)

data Fruit = Apple Int | Pear { ripeness :: Number }
derive instance Generic Fruit _
derive instance Eq Fruit
derive instance Ord Fruit
instance Show Fruit where show = genericShow
instance Pretty Fruit where
  pretty = case _ of
    Apple n -> show n <> " apples"
    Pear { ripeness } -> "pear@" <> show ripeness
instance Summary Fruit where
  summary fruit = "<" <> pretty fruit <> ">"
  weight = case _ of
    Apple n -> n * 100
    Pear { ripeness } -> if ripeness > 0.5 then 180 else 150
instance Tagged "fruit" Fruit

newtype Basket = Basket (Array Fruit)
instance Pretty Basket where
  pretty (Basket fruits) = fruits <#> pretty # Array.intercalate " + "
instance Summary Basket where
  summary basket = "basket(" <> pretty basket <> ")"
  weight (Basket fruits) = fruits <#> weightOf # Array.foldl (+) 0
    where
    weightOf = case _ of
      Apple n -> n
      Pear _ -> 2
instance Tagged "basket" Basket

