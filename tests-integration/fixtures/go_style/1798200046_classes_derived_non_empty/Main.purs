module T.Derive2 where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Eq.Generic (genericEq)
import Data.Foldable (class Foldable, foldMap, foldr, length, sum)
import Data.Traversable (class Traversable, traverse)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, un)
import Data.Ord.Generic (genericCompare)
import Data.Semigroup.Foldable (foldMap1)
import Data.Show.Generic (genericShow)
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Effect.Console (log)
import Data.Ord.Max (Max(..))
import Data.Ord.Min (Min(..))
import Data.Monoid.Conj (Conj(..))
import Data.Monoid.Disj (Disj(..))
import Data.Monoid.Endo (Endo(..))
import Data.Monoid.Dual (Dual(..))
import Safe.Coerce (coerce)

data Event a
  = Clicked { x :: Int, y :: Int, payload :: a }
  | Typed String a
  | Batch (Array (Event a))
  | Timed (Number -> a)
  | Nothing'
  | Pairs (Array (Int /\ a))
  | Opt (Maybe a)

derive instance Functor Event

describeEvent :: Event String -> String
describeEvent = case _ of
  Clicked r -> "clicked " <> show r
  Typed s a -> "typed " <> s <> a
  Batch es -> "batch[" <> (es <#> describeEvent # Array.intercalate ";") <> "]"
  Timed f -> "timed " <> f 2.5
  Nothing' -> "nothing"
  Pairs ps -> "pairs " <> show ps
  Opt m -> "opt " <> show m

data Box a = Box a (Array a) | Empty
derive instance Functor Box
derive instance Foldable Box
derive instance Traversable Box
derive instance Eq a => Eq (Box a)
derive instance Ord a => Ord (Box a)
derive instance Generic (Box a) _
instance Show a => Show (Box a) where show = genericShow

newtype Items a = Items (Array a)
derive newtype instance Functor Items
derive newtype instance Foldable Items
derive newtype instance Show a => Show (Items a)
derive newtype instance Semigroup (Items a)
derive newtype instance Monoid (Items a)
derive instance Newtype (Items a) _

newtype UserId = UserId Int
derive newtype instance Eq UserId
derive newtype instance Ord UserId
derive newtype instance Show UserId
derive instance Newtype UserId _

data Status = Active | Banned { reason :: String, days :: Int } | Pending Int String
derive instance Generic Status _
instance Show Status where show = genericShow
instance Eq Status where eq = genericEq
instance Ord Status where compare = genericCompare

newtype Wrapped = Wrapped { inner :: Array (Maybe Status) }
derive instance Generic Wrapped _
instance Show Wrapped where show = genericShow

main :: Effect Unit
main = do
  let events = [ Clicked { x: 1, y: -2, payload: 3 }, Typed "ab" 4, Batch [ Nothing', Opt (Just 5), Opt Nothing ], Timed (\n -> if n > 1.0 then 6 else 7), Pairs [ 1 /\ 8, 2 /\ 9 ] ]
  events <#> map (\n -> show (n * 10)) <#> describeEvent # Array.intercalate "\n" # log
  let boxes = [ Box 3 [ 1, 2 ], Empty, Box 1 [], Box 3 [ 0 ] ]
  log (show (Array.sort boxes) <> show (boxes <#> sum) <> show (boxes <#> length :: Array Int))
  log (show (boxes <#> map show) <> show (traverse (\n -> if n >= 0 then Just n else Nothing) (Box 1 [ 2, -1 ])))
  log (show (Items [ 1, 2 ] <> mempty <> Items [ 3 ]) <> show (map (_ + 1) (Items [ 1 ])) <> show (sum (Items [ 5, 6 ])))
  let byUser = Map.fromFoldable [ UserId 3 /\ "c", UserId (-1) /\ "neg", UserId 10 /\ "ten" ]
  log (show byUser <> show (Map.lookup (UserId 10) byUser))
  log (show (coerce (Map.fromFoldable [ 1 /\ UserId 5 ]) :: Map Int Int))
  log (show (map (un UserId) (Map.keys byUser # Array.fromFoldable)))
  let statuses = [ Pending 2 "b", Banned { reason: "spam", days: 3 }, Active, Pending 2 "a", Banned { reason: "abuse", days: 30 } ]
  log (show (Array.sort statuses))
  log (show (Array.nub statuses) <> show (Array.elem Active statuses))
  log (show (Wrapped { inner: [ Just Active, Nothing, Just (Pending (-1) "\"q\"") ] }))
  case NEA.fromArray [ 4, -2, 9 ] of
    Nothing -> pure unit
    Just nums -> do
      log (show (foldMap1 Max nums) <> show (foldMap1 Min nums))
      log (show (foldMap1 (\n -> { biggest: Max n, smallest: Min n, total: [ n ] }) nums))
  log (show (foldMap (\n -> Conj (n > 0)) [ 1, 2 ]) <> show (foldMap (\n -> Disj (n > 5)) [ 1, 2 ]))
  log (show (un Endo (foldMap (\n -> Endo (_ * n)) [ 2, 3 ]) 1) <> show (un Dual (foldMap (\s -> Dual [ s ]) [ "a", "b", "c" ])))
