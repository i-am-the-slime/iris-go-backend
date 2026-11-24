module T.Derive where

import Prelude

import Data.Array as Array
import Data.Bounded.Generic (genericBottom, genericTop)
import Data.Enum (class BoundedEnum, class Enum, enumFromTo, fromEnum, pred, succ, toEnum, upFromIncluding)
import Data.Enum.Generic (genericCardinality, genericFromEnum, genericPred, genericSucc, genericToEnum)
import Data.Eq.Generic (genericEq)
import Data.Function (on)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Maybe.First (First(..))
import Data.Maybe.Last (Last(..))
import Data.Monoid.Additive (Additive(..))
import Data.Monoid.Multiplicative (Multiplicative(..))
import Data.Newtype (class Newtype, over, over2, un, unwrap, wrap)
import Data.Ord.Generic (genericCompare)
import Data.Show.Generic (genericShow)
import Data.Foldable (fold, foldMap, maximum, minimum)
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Effect.Console (log)
import Safe.Coerce (coerce)

data Suit = Clubs | Diamonds | Hearts | Spades
derive instance Eq Suit
derive instance Ord Suit
derive instance Generic Suit _
instance Show Suit where show = genericShow
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

data Card = Card Int Suit | Joker
derive instance Eq Card
derive instance Ord Card
derive instance Generic Card _
instance Show Card where show = genericShow

data Expr a = Lit a | Add (Expr a) (Expr a) | Neg (Expr a) | Many (Array (Expr a)) | Pair a a | Labelled { label :: String, value :: a }
derive instance Functor (Expr)
derive instance Generic (Expr a) _
instance Show a => Show (Expr a) where show e = genericShow e
instance Eq a => Eq (Expr a) where eq a b = genericEq a b
derive instance Ord a => Ord (Expr a)

newtype Score = Score Int
derive newtype instance Show Score
derive newtype instance Eq Score
derive newtype instance Ord Score
derive newtype instance Semiring Score
derive instance Newtype Score _

newtype Name = Name String
derive newtype instance Show Name
derive newtype instance Eq Name
derive newtype instance Ord Name
derive newtype instance Semigroup Name
derive newtype instance Monoid Name
derive instance Newtype Name _

newtype Wrapper = Wrapper { name :: Name, score :: Score }
derive instance Newtype Wrapper _
derive instance Generic Wrapper _
instance Show Wrapper where show = genericShow
derive instance Eq Wrapper
derive instance Ord Wrapper

type Player = { name :: String, score :: Int, ratio :: Number }

main :: Effect Unit
main = do
  log (show (Array.sort [ Spades, Clubs, Hearts, Diamonds ]))
  log (show (bottom :: Suit) <> show (top :: Suit) <> show (succ Hearts) <> show (pred Clubs) <> show (succ Spades))
  log (show (enumFromTo Diamonds Spades :: Array Suit) <> show (upFromIncluding Hearts :: Array Suit))
  log (show (fromEnum Spades) <> show (toEnum 2 :: Maybe Suit) <> show (toEnum 9 :: Maybe Suit))
  let cards = [ Card 10 Hearts, Joker, Card (-2) Spades, Card 10 Clubs, Card 3 Hearts ]
  log (show (Array.sort cards))
  log (show (maximum cards) <> show (minimum cards))
  log (show (compare Joker (Card 1 Clubs)) <> show (max (Card 1 Clubs) (Card 1 Spades)))
  log (show (Array.sortWith (\c -> case c of
      Card n _ -> -n
      Joker -> 0) cards))
  let expr = Many [ Add (Lit 1) (Neg (Lit (-2))), Pair 3 4, Labelled { label: "x", value: 5 } ]
  log (show (expr <#> (_ * 10)))
  log (show (map show expr))
  log (show (expr == expr) <> show (expr == (expr <#> (_ + 0))) <> show (expr == (expr <#> (_ + 1))))
  log (show (compare (Lit 1) (Add (Lit 0) (Lit 0))) <> show (compare (Pair 1 2) (Pair 1 3)))
  log (show (Array.sort [ Lit 3, Neg (Lit 1), Lit (-1), Pair 0 0, Labelled { label: "b", value: 1 }, Labelled { label: "a", value: 2 } ]))
  log (show (Score 3 + Score 4 * Score 5) <> show (Score 1 < Score 2) <> show (zero :: Score) <> show (one :: Score))
  log (show (Name "a" <> Name "b" <> mempty) <> show (fold [ Name "x", Name "y" ]))
  let scores = [ Score 5, Score (-1), Score 3 ]
  log (show (coerce scores :: Array Int))
  log (show (coerce [ 1, 2 ] :: Array Score))
  log (show (coerce { a: Score 1, b: [ Name "n" ] } :: { a :: Int, b :: Array String }))
  log (show (un Score (Score 9)) <> show (over Score (_ + 1) (Score 9) :: Score) <> show (unwrap (Name "u")) <> show (wrap 7 :: Score))
  log (show (over2 Score (+) (Score 1) (Score 2) :: Score))
  let w = Wrapper { name: Name "w", score: Score 1 }
  log (show w <> show (w == w) <> show (compare w (Wrapper { name: Name "w", score: Score 2 })))
  let players = [ { name: "bo", score: 3, ratio: -0.5 }, { name: "al", score: 3, ratio: 1.0e21 }, { name: "cy", score: -10, ratio: 0.1 } ] :: Array Player
  log (show (Array.sortBy (compare `on` _.score) players))
  log (show (Array.sortWith _.name players))
  log (show (Array.sort players))
  log (show (Array.sortWith (\p -> p.score /\ p.name) players))
  log (show (foldMap (\p -> Additive p.score) players) <> show (foldMap (\p -> Multiplicative p.score) players))
  log (show (foldMap (\p -> First (Just p.name)) players) <> show (foldMap (\p -> Last (Just p.name)) players))
  log (show (foldMap (\p -> { total: Additive p.score, names: [ p.name ] }) players))
  log (show ({ a: [ 1 ], b: "x" } <> { a: [ 2 ], b: "y" }) <> show (mempty :: { a :: Array Int, b :: String }))
  log (show (Array.sort [ -3.5, 2.0, -0.0, 0.0, 1.0e-7, -1.0e300 ]))
  log (show (Array.sort [ "b", "B", "a", "ä", "", "Z" ]))
  log (show (compare [ 1, 2 ] [ 1 ]) <> show (compare (Just 1) Nothing) <> show (max "abc" "abd"))
