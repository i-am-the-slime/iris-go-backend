module T.Chains where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Symbol (class IsSymbol, reflectSymbol)
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Effect.Console (log)
import Prim.RowList as RL
import Prim.Row as Row
import Record as Record
import Type.Proxy (Proxy(..))

-- instance chains
class Pretty a where
  pretty :: a -> String

instance Pretty String where
  pretty s = "'" <> s <> "'"
else instance Pretty Int where
  pretty n = "#" <> show n
else instance Pretty Boolean where
  pretty b = if b then "yes" else "no"
else instance Pretty a => Pretty (Array a) where
  pretty xs = "<" <> (xs <#> pretty # Array.intercalate " ") <> ">"
else instance Pretty a => Pretty (Maybe a) where
  pretty = case _ of
    Nothing -> "-"
    Just a -> pretty a
else instance (Pretty a, Pretty b) => Pretty (a /\ b) where
  pretty (a /\ b) = "(" <> pretty a <> " , " <> pretty b <> ")"
else instance (RL.RowToList row list, PrettyFields list row) => Pretty (Record row) where
  pretty record = "{" <> (prettyFields (Proxy :: _ list) record # Array.intercalate "; ") <> "}"
else instance Show a => Pretty a where
  pretty a = "show:" <> show a

class PrettyFields :: RL.RowList Type -> Row Type -> Constraint
class PrettyFields list row | list -> row where
  prettyFields :: Proxy list -> Record row -> Array String

instance PrettyFields RL.Nil () where
  prettyFields _ _ = []
instance
  ( IsSymbol name
  , Pretty value
  , PrettyFields tail tailRow
  , Row.Cons name value tailRow row
  , Row.Lacks name tailRow
  ) =>
  PrettyFields (RL.Cons name value tail) row where
  prettyFields _ record = do
    let fieldName = Proxy :: _ name
    let here = reflectSymbol fieldName <> "=" <> pretty (Record.get fieldName record)
    let rest = prettyFields (Proxy :: _ tail) (Record.delete fieldName record)
    Array.cons here rest

-- multi-param with fundep
class Container f a | f -> a where
  contents :: f -> Array a

newtype Bag = Bag (Array Int)
newtype Words = Words String

instance Container Bag Int where
  contents (Bag xs) = xs
instance Container Words String where
  contents (Words s) = [ s, s <> s ]

sumContents :: forall f. Container f Int => f -> Int
sumContents = contents >>> Array.foldl (+) 0

-- HKT class
class Boxy f where
  boxUp :: forall a. a -> f a
  unboxAll :: forall a. f a -> Array a

instance Boxy Array where
  boxUp = Array.singleton
  unboxAll = identity
instance Boxy Maybe where
  boxUp = Just
  unboxAll = case _ of
    Nothing -> []
    Just a -> [ a ]
instance Boxy (Either String) where
  boxUp = Right
  unboxAll = case _ of
    Left _ -> []
    Right a -> [ a ]

roundTrip :: forall @f a. Boxy f => a -> Array a
roundTrip a = unboxAll (boxUp a :: f a)

-- method with extra constraint
class Collect f where
  collectShown :: forall a. Show a => f a -> String

instance Collect Array where
  collectShown xs = xs <#> show # Array.intercalate ","
instance Collect Maybe where
  collectShown = case _ of
    Nothing -> "none"
    Just a -> show a

-- mutually recursive instances via data types
data Tree = Node String Forest
newtype Forest = Forest (Array Tree)

instance Show Tree where
  show (Node name forest) = "Node " <> show name <> " " <> show forest
instance Show Forest where
  show (Forest trees) = "Forest " <> show trees

-- function instance
class Apply2 a where
  apply2 :: a -> String
instance Apply2 (Int -> Int) where
  apply2 f = show (f (f 3))
else instance Apply2 (String -> String) where
  apply2 f = f (f "x")

main :: Effect Unit
main = do
  log (pretty "hi")
  log (pretty 3)
  log (pretty [ true, false ])
  log (pretty (Just [ "a", "b" ]))
  log (pretty (1 /\ "two"))
  log (pretty { name: "Ada", age: 36, tags: [ "x" ], nested: { ok: true, n: Nothing :: Maybe Int } })
  log (pretty 2.5)
  log (pretty [ 'c', 'd' ])
  log (pretty (Left 1 :: Either Int String))
  log (show (sumContents (Bag [ 1, 2, 3 ])))
  log (show (contents (Words "ab")))
  log (show (roundTrip @Array 1) <> show (roundTrip @Maybe "m") <> show (roundTrip @(Either String) true))
  log (collectShown [ 1, 2 ] <> " " <> collectShown (Just "q") <> " " <> collectShown (Nothing :: Maybe Int))
  log (show (Node "root" (Forest [ Node "a" (Forest []), Node "b" (Forest [ Node "c" (Forest []) ]) ])))
  log (apply2 ((_ * 2) :: Int -> Int) <> " " <> apply2 (\s -> s <> "!" :: String))
