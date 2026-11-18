module Main where

import Prelude

import Data.Exists (Exists, mkExists, runExists)
import Data.String as String

-- A free applicative: `Apply` hides the intermediate type of each application
-- inside `Exists`, so `map` recurses at `Ap (x -> a)` for every hidden `x`.
data Ap a
  = Done a
  | Field String a
  | Apply (Exists (ApplyE a))

data ApplyE a x = ApplyE (Ap (x -> a)) (Ap x)

instance Functor Ap where
  map f = case _ of
    Done a -> Done (f a)
    Field name a -> Field name (f a)
    Apply e -> runExists (\(ApplyE function argument) -> Apply (mkExists (ApplyE (map (f <<< _) function) argument))) e

instance Apply Ap where
  apply function argument = Apply (mkExists (ApplyE function argument))

instance Applicative Ap where
  pure = Done

run :: forall a. Ap a -> a
run = case _ of
  Done a -> a
  Field _ a -> a
  Apply e -> runExists (\(ApplyE function argument) -> run function (run argument)) e

names :: forall a. Ap a -> Array String
names = case _ of
  Done _ -> []
  Field name _ -> [ name ]
  Apply e -> runExists (\(ApplyE function argument) -> names function <> names argument) e

type Person = { name :: String, age :: Int, admin :: Boolean }

person :: Ap Person
person = { name: _, age: _, admin: _ }
  <$> Field "name" "ada"
  <*> map (_ * 2) (Field "age" 18)
  <*> Field "admin" true

greeting :: Ap String
greeting = (\p n -> p.name <> " is " <> show p.age <> " " <> show n) <$> person <*> Field "count" 3.5

main :: Array String
main =
  [ String.joinWith "," (names person)
  , show (run person)
  , run (map String.toUpper greeting)
  , show (String.length (run greeting))
  ]
