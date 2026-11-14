module Compat.Coercions.Coerce where

import Prelude

import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested ((/\))
import Data.Monoid.Additive (Additive(..))
import Data.Monoid.Multiplicative (Multiplicative(..))
import Data.Newtype (class Newtype, alaF, over, over2, un, under, unwrap, wrap)
import Data.Foldable (foldMap)
import Effect (Effect)
import Effect.Console (log)
import Safe.Coerce (coerce)
import Unsafe.Coerce (unsafeCoerce)

newtype UserId = UserId Int
derive instance Newtype UserId _
derive newtype instance Show UserId
derive newtype instance Eq UserId
derive newtype instance Ord UserId
derive newtype instance Semiring UserId

newtype Name = Name String
derive instance Newtype Name _
derive newtype instance Show Name
derive newtype instance Semigroup Name

newtype Wrapped f a = Wrapped (f a)
derive instance Newtype (Wrapped f a) _

newtype Score = Score { points :: Int, bonus :: Int }
derive instance Newtype Score _

type Point = { x :: Number, y :: Number }
type Vector = { x :: Number, y :: Number }

main :: Effect Unit
main = do
  let ids = coerce [ 1, 2, 3 ] :: Array UserId
  log (show ids)
  log (show (coerce ids :: Array Int))
  log (show (coerce (Just (UserId 5)) :: Maybe Int))
  log (show (unwrap (coerce (Wrapped [ UserId 9 ]) :: Wrapped Array Int)))
  let directory = coerce (Map.fromFoldable [ UserId 1 /\ Name "ann" ]) :: Map.Map UserId String
  log (show (Map.lookup (UserId 1) directory))
  log (show (UserId 2 + UserId 3) <> " " <> show (Name "a" <> Name "b"))
  log (show (over UserId (_ * 2) (UserId 21) :: UserId) <> " " <> show (under UserId (_ + UserId 1) 1 :: Int))
  log (show (alaF Additive foldMap identity [ 1, 2, 3 ] :: Int) <> " " <> show (alaF Multiplicative foldMap identity [ 1, 2, 3, 4 ] :: Int))
  log (show (un Score (Score { points: 3, bonus: 1 })).points)
  log (show (over2 UserId (+) (UserId 1) (UserId 2) :: UserId))
  let point = { x: 1.0, y: 2.0 } :: Point
  let vector = unsafeCoerce point :: Vector
  log (show vector.x)
  log (show (unsafeCoerce (UserId 77) :: Int))
  log (show (wrap 4 :: UserId))
