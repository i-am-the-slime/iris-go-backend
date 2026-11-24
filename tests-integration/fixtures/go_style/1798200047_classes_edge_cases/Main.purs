module T.Edge2 where

import Prelude

import Data.Array as Array
import Data.Eq (class Eq1)
import Data.Ord (class Ord1)
import Data.List.NonEmpty as NEL
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.NonEmpty ((:|))
import Data.Number as Number
import Data.Set as Set
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Console (log)
import Data.Bifunctor (class Bifunctor, bimap, lmap, rmap)
import Data.Profunctor (class Profunctor, dimap)

data Wrap f a = Wrap (f a) Int
derive instance (Eq1 f, Eq a) => Eq (Wrap f a)
derive instance (Ord1 f, Ord a) => Ord (Wrap f a)
instance Show (f a) => Show (Wrap f a) where
  show (Wrap inner n) = "Wrap(" <> show inner <> "," <> show n <> ")"

newtype Money = Money Number
derive instance Newtype Money _
derive newtype instance Show Money
derive newtype instance Eq Money
derive newtype instance Ord Money
derive newtype instance Semiring Money
derive newtype instance Ring Money
derive newtype instance CommutativeRing Money
derive newtype instance EuclideanRing Money
derive newtype instance DivisionRing Money

data Pair a b = Pair a b
derive instance (Eq a, Eq b) => Eq (Pair a b)
instance Bifunctor Pair where
  bimap f g (Pair a b) = Pair (f a) (g b)
instance (Show a, Show b) => Show (Pair a b) where
  show (Pair a b) = "Pair " <> show a <> " " <> show b

newtype Fn a b = Fn (a -> b)
instance Profunctor Fn where
  dimap pre post (Fn f) = Fn (pre >>> f >>> post)

runFn :: forall a b. Fn a b -> a -> b
runFn (Fn f) = f

main :: Effect Unit
main = do
  log (show (Array.sort [ Wrap (Just 2) 1, Wrap Nothing 5, Wrap (Just 1) 9 ]) <> show (Wrap [ 1 ] 0 == Wrap [ 1 ] 0))
  log (show (Money 1.5 + Money 2.25 * Money 2.0 - Money 0.5) <> show (Money 7.0 / Money 2.0) <> show (recip (Money 4.0)) <> show (negate (Money 1.0)))
  log (show (bimap (_ + 1) show (Pair 1 2)) <> show (lmap show (Pair 1 'c')) <> show (rmap (_ * 2) (Pair "a" 4)))
  log (show (runFn (dimap (_ + 1) show (Fn (_ * 10))) 4))
  let nan = Number.nan
  log (show (Array.sort [ 3.0, nan, -1.0, 0.0, nan, 2.0 ]))
  log (show (compare nan 1.0) <> show (compare 1.0 nan) <> show (max nan 1.0) <> show (min nan 1.0) <> show (nan == nan) <> show (nan /= nan))
  log (show (Map.fromFoldable [ nan /\ "a", 1.0 /\ "b", nan /\ "c" ]))
  log (show (Map.size (Map.fromFoldable [ nan /\ "a", nan /\ "c" ])) <> show (Map.lookup nan (Map.fromFoldable [ nan /\ "a" ])))
  log (show (Set.fromFoldable [ 0.0, -0.0, 1.0 ]) <> show (Map.fromFoldable [ -0.0 /\ "neg", 0.0 /\ "pos" ]))
  log (show (Array.nub [ nan, nan, 1.0 ]) <> show (Array.elem nan [ nan ]) <> show (Array.sortWith identity [ nan, 1.0, nan, 0.0 ]))
  log (show (Map.lookupLE 5 (Map.fromFoldable [ 1 /\ "a", 7 /\ "b" ])) <> show (Map.lookupGE 5 (Map.fromFoldable [ 1 /\ "a", 7 /\ "b" ])))
  log (show (Map.fromFoldable [ 1 /\ "a" ] <> Map.fromFoldable [ 1 /\ "b", 2 /\ "c" ]) <> show (Set.fromFoldable [ 1 ] <> Set.fromFoldable [ 0 ]))
  log (show (NEL.fromFoldable [ 1, 2 ]) <> show (1 :| [ 2, 3 ]) <> show (NEL.head (NEL.singleton 'x')))
  log (show (Number.fromString "1e400") <> show (1.0e308 * 10.0) <> show (Number.isFinite (1.0 / 0.0)) <> show (0.0 / 0.0))
