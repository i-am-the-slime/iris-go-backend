module Compat.Exotic.RankN where

import Prelude

import Data.Array as Array
import Data.Foldable as Data.Foldable
import Data.String.CodeUnits as Data.String.CodeUnits
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Console (log)

type Transformer = { apply :: forall a. Array a -> Array a, name :: String }

newtype NaturalTransformation f g = NaturalTransformation (forall a. f a -> g a)

runNaturalTransformation :: forall f g a. NaturalTransformation f g -> f a -> g a
runNaturalTransformation (NaturalTransformation f) = f

applyBoth :: (forall a. Array a -> Array a) -> { ints :: Array Int, strings :: Array String } -> String
applyBoth f { ints, strings } = show (f ints) <> " " <> show (f strings)

newtype Church = Church (forall a. (a -> a) -> a -> a)

church :: Int -> Church
church 0 = Church \_ z -> z
church n = case church (n - 1) of Church previous -> Church \s z -> s (previous s z)

unchurch :: Church -> Int
unchurch (Church n) = n (_ + 1) 0

plus :: Church -> Church -> Church
plus (Church a) (Church b) = Church \s z -> a s (b s z)

times :: Church -> Church -> Church
times (Church a) (Church b) = Church \s -> a (b s)

newtype Parser a = Parser (forall r. String -> (String -> a -> r) -> (String -> r) -> r)

runParser :: forall a. Parser a -> String -> Maybe a
runParser (Parser p) input = p input (\_ a -> Just a) (\_ -> Nothing)

character :: Char -> Parser Char
character c = Parser \input success failure -> case Array.uncons (toChars input) of
  Just { head, tail } | head == c -> success (fromChars tail) c
  _ -> failure "unexpected"
  where
  toChars = Data.String.CodeUnits.toCharArray
  fromChars = Data.String.CodeUnits.fromCharArray

andThen :: forall a b. Parser a -> Parser b -> Parser { first :: a, second :: b }
andThen (Parser p) (Parser q) = Parser \input success failure ->
  p input (\rest a -> q rest (\rest' b -> success rest' { first: a, second: b }) failure) failure

type Lens s a = forall f. Functor f => (a -> f a) -> s -> f s

newtype Const' a b = Const' a
instance Functor (Const' a) where
  map _ (Const' a) = Const' a

newtype Id a = Id a
instance Functor Id where
  map f (Id a) = Id (f a)

firstLens :: forall a b. Lens { first :: a, second :: b } a
firstLens f record = map (\a -> record { first = a }) (f record.first)

view :: forall s a. Lens s a -> s -> a
view lens s = case lens Const' s of Const' a -> a

setter :: forall s a. Lens s a -> a -> s -> s
setter lens a s = case lens (\_ -> Id a) s of Id result -> result

main :: Effect Unit
main = do
  let transformers = [ { apply: Array.reverse, name: "reverse" }, { apply: Array.take 1, name: "take1" } ] :: Array Transformer
  Data.Foldable.for_ transformers \t -> log (t.name <> ": " <> show (t.apply [ 1, 2, 3 ]) <> " " <> show (t.apply [ "a", "b" ]))
  log (applyBoth (Array.drop 1) { ints: [ 1, 2 ], strings: [ "x", "y" ] })
  log (show (runNaturalTransformation (NaturalTransformation Array.head) [ 7, 8 ]))
  log (show (unchurch (plus (church 3) (times (church 4) (church 5)))))
  log (show (runParser (character 'a' `andThen` character 'b') "abc"))
  log (show (runParser (character 'a' `andThen` character 'b') "aXc"))
  let pair = { first: 1, second: "s" }
  log (show (view firstLens pair) <> " " <> show (setter firstLens 99 pair))
