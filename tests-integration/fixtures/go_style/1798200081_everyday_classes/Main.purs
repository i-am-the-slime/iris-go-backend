module Fun.Classes where

import Prelude

import Control.Lazy (fix, defer)
import Data.Array ((..), (:))
import Data.Bounded.Generic (genericBottom, genericTop)
import Data.Enum (class Enum, class BoundedEnum, enumFromTo, succ, pred, fromEnum, toEnum, upFromIncluding)
import Data.Enum.Generic (genericSucc, genericPred, genericCardinality, genericToEnum, genericFromEnum)
import Data.Eq.Generic (genericEq)
import Data.Foldable (class Foldable, foldMap, foldl, foldr, for_)
import Data.Generic.Rep (class Generic)
import Data.Lazy as Lazy
import Data.List.Lazy as LazyList
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Ord.Generic (genericCompare)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Traversable (class Traversable, traverse, sequenceDefault)
import Data.Tuple.Nested ((/\), type (/\))
import Data.Variant (Variant, inj, on, case_, match)
import Effect (Effect)
import Effect.Console (log)
import Record as Record
import Type.Proxy (Proxy(..))
import Data.Enum (Cardinality)

data Colour = Red | Green | Blue

derive instance Generic Colour _
instance Show Colour where show = genericShow
instance Eq Colour where eq = genericEq
instance Ord Colour where compare = genericCompare
instance Bounded Colour where
  top = genericTop
  bottom = genericBottom
instance Enum Colour where
  succ = genericSucc
  pred = genericPred
instance BoundedEnum Colour where
  cardinality = genericCardinality
  toEnum = genericToEnum
  fromEnum = genericFromEnum

data Tree a = Leaf | Node (Tree a) a (Tree a)

derive instance Generic (Tree a) _
derive instance Eq a => Eq (Tree a)
derive instance Ord a => Ord (Tree a)
derive instance Functor Tree
derive instance Foldable Tree
derive instance Traversable Tree
instance Show a => Show (Tree a) where
  show tree = genericShow tree

data Expr = Num Int | Add Expr Expr | Mul Expr Expr | Neg Expr

derive instance Generic Expr _
instance Show Expr where
  show expr = genericShow expr

class Describable a where
  describe :: a -> String
  name :: Proxy a -> String

instance Describable Int where
  describe n = "int " <> show n
  name _ = "Int"

instance Describable Boolean where
  describe b = if b then "yes" else "no"
  name _ = "Boolean"

instance Describable a => Describable (Array a) where
  describe items = "[" <> foldMap describe items <> "]"
  name _ = "Array " <> name (Proxy :: Proxy a)

instance (Describable a, Describable b) => Describable (Maybe a /\ b) where
  describe (a /\ b) = foldMap describe a <> "&" <> describe b
  name _ = "Pair"

class Describable a <= Fancy a where
  fancy :: a -> String

instance Fancy Int where
  fancy n = "*" <> describe n <> "*"

describeTwice :: forall a. Fancy a => a -> String
describeTwice a = fancy a <> "|" <> describe a

nameOf :: forall @a. Describable a => String
nameOf = name (Proxy :: Proxy a)

showAll :: (forall a. Show a => a -> String) -> String
showAll render = render 1 <> render true <> render "s"

insert :: forall a. Ord a => a -> Tree a -> Tree a
insert value = case _ of
  Leaf -> Node Leaf value Leaf
  node@(Node left current right)
    | value < current -> Node (insert value left) current right
    | value > current -> Node left current (insert value right)
    | otherwise -> node

evaluate :: Expr -> Int
evaluate = case _ of
  Num n -> n
  Add a b -> evaluate a + evaluate b
  Mul a b -> evaluate a * evaluate b
  Neg a -> negate (evaluate a)

isEven :: Int -> Boolean
isEven 0 = true
isEven n = isOdd (n - 1)

isOdd :: Int -> Boolean
isOdd 0 = false
isOdd n = isEven (n - 1)

type Shape = Variant (circle :: Number, square :: Int, label :: String)

area :: Shape -> String
area = case_
  # on (Proxy :: Proxy "circle") (\r -> "circle " <> show (r * r))
  # on (Proxy :: Proxy "square") (\s -> "square " <> show (s * s))
  # on (Proxy :: Proxy "label") identity

areaMatch :: Shape -> String
areaMatch = match
  { circle: \r -> "c" <> show r
  , square: \s -> "s" <> show s
  , label: \l -> "l" <> l
  }

getX :: forall r. { x :: Int | r } -> Int
getX = _.x

bumpX :: forall r. { x :: Int | r } -> { x :: Int | r }
bumpX record = record { x = record.x + 1 }

fibs :: LazyList.List Int
fibs = fix \self -> LazyList.cons 0 (LazyList.cons 1 (defer \_ -> LazyList.zipWith (+) self (LazyList.drop 1 self)))

main :: Effect Unit
main = do
  log $ show (enumFromTo Red Blue :: Array Colour)
  log $ show [ succ Red, succ Blue, pred Red ]
  log $ show (fromEnum Blue) <> show (toEnum 1 :: Maybe Colour) <> show (toEnum 5 :: Maybe Colour)
  log $ show (top :: Colour) <> show (bottom :: Colour) <> show (compare Red Blue) <> show (Red == Red)
  log $ show (upFromIncluding Green :: Array Colour)
  let tree = foldl (flip insert) Leaf [ 5, 3, 8, 1, 4 ]
  log $ show tree
  log $ show (tree <#> (_ * 2))
  log $ show (foldr (:) [] tree) <> show (foldl (flip (:)) [] tree)
  log $ show (foldMap show tree)
  log $ show (traverse (\n -> if n > 0 then Just n else Nothing) tree)
  log $ show (sequenceDefault (map Just tree))
  log $ show (insert 4 tree == tree) <> show (compare tree Leaf)
  let expr = Add (Num 2) (Mul (Num 3) (Neg (Num 4)))
  log $ show expr <> " = " <> show (evaluate expr)
  log $ describe [ 1, 2 ] <> describe true <> describe (Just 1 /\ false)
  log $ describeTwice 5
  log $ nameOf @(Array (Array Int)) <> nameOf @Boolean
  log $ showAll show
  log $ show (isEven 100000) <> show (isOdd 7)
  let shapes = [ inj (Proxy :: Proxy "circle") 2.0, inj (Proxy :: Proxy "square") 3, inj (Proxy :: Proxy "label") "hi" ] :: Array Shape
  log $ show (shapes <#> area) <> show (shapes <#> areaMatch)
  log $ show (getX { x: 1, y: "y" }) <> show (bumpX { x: 1, z: true })
  log $ show (Record.insert (Proxy :: Proxy "added") 5 { a: 1 })
  log $ show (Record.get (Proxy :: Proxy "a") { a: 1, b: 2 })
  log $ show (Record.merge { a: 1 } { b: "two" })
  log $ show { "weird key": 1, "with\"quote": 2, normal: 3 }
  let table = Map.fromFoldable [ "b" /\ 2, "a" /\ 1, "c" /\ 3 ]
  log $ show table
  log $ show (Map.toUnfoldable (Map.insert "aa" 0 table) :: Array _)
  log $ show (Map.keys table) <> show (Map.values table)
  log $ show (Map.unionWith (+) table (Map.singleton "a" 10))
  log $ show (Set.fromFoldable [ 3, 1, 2, 3 ]) <> show (Set.toUnfoldable (Set.fromFoldable [ 3, 1, 2 ]) :: Array Int)
  log $ show (LazyList.take 15 fibs)
  let lazyValue = Lazy.defer \_ -> 6 * 7
  log $ show (Lazy.force lazyValue) <> show (Lazy.force (lazyValue <#> (_ + 1)))
  for_ (1 .. 2) \i -> log (show i)
