module T.Adv where

import Prelude

import Control.Monad.State (State, evalState, get, modify_, put, runState)
import Control.Monad.Reader (Reader, ask, asks, runReader, local)
import Control.Monad.Writer (Writer, runWriter, tell)
import Data.Array as Array
import Data.Foldable (class Foldable, foldl, foldMap, foldr, traverse_)
import Data.Traversable (class Traversable, traverse, sequence)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Either (Either(..), either)
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Effect.Console (log)

-- superclass access through subclass dict
sameAndBigger :: forall a. Ord a => a -> a -> String
sameAndBigger x y = show (x == y) <> show (x > y)
  where
  show b = if b then "T" else "F"

-- local polymorphic helper with constraint in where
summarize :: forall a. Show a => Ord a => Array a -> String
summarize items = describeAll items <> " max=" <> showMax items
  where
  describeAll :: forall b. Show b => Array b -> String
  describeAll = map show >>> Array.intercalate ","
  showMax = Array.sort >>> Array.last >>> map show >>> fromMaybe "none"

-- higher rank
applyToBoth :: (forall x. Show x => x -> String) -> Int /\ String -> String
applyToBoth f (n /\ s) = f n <> f s

-- user Functor/Foldable/Traversable instances
data Rose a = Rose a (Array (Rose a))

instance Functor Rose where
  map f (Rose a kids) = Rose (f a) (kids <#> map f)
instance Foldable Rose where
  foldr f z (Rose a kids) = f a (foldr (\kid acc -> foldr f acc kid) z kids)
  foldl f z (Rose a kids) = foldl (\acc kid -> foldl f acc kid) (f z a) kids
  foldMap f (Rose a kids) = f a <> foldMap (foldMap f) kids
instance Traversable Rose where
  traverse f (Rose a kids) = Rose <$> f a <*> traverse (traverse f) kids
  sequence = traverse identity
instance Show a => Show (Rose a) where
  show (Rose a kids) = "Rose " <> show a <> " " <> show kids

-- genuine polymorphic recursion (nested datatype)
data Nested a = Flat a | Nest (Nested (Array a))

instance Show a => Show (Nested a) where
  show (Flat a) = "Flat " <> show a
  show (Nest inner) = "Nest (" <> show inner <> ")"

depth :: forall a. Nested a -> Int
depth = case _ of
  Flat _ -> 0
  Nest inner -> 1 + depth inner

-- class over HKT with superclass Functor and default-ish
class Functor f <= Shelf f where
  shelve :: forall a. a -> f a
  items :: forall a. f a -> Array a

instance Shelf Array where
  shelve = pure
  items = identity
instance Shelf Rose where
  shelve a = Rose a []
  items = Array.fromFoldable

restock :: forall f. Shelf f => f Int -> Array Int
restock shelf = shelf <#> (_ + 1) <#> (_ * 2) # items

-- monad transformer-ish
counter :: State Int (Array Int)
counter = do
  modify_ (_ + 1)
  a <- get
  modify_ (_ * 10)
  b <- get
  put (b - 3)
  c <- get
  pure [ a, b, c ]

labelTree :: forall a. Rose a -> State Int (Rose (Int /\ a))
labelTree = traverse \a -> do
  n <- get
  put (n + 1)
  pure (n /\ a)

configured :: Reader { indent :: Int, name :: String } String
configured = do
  name <- asks _.name
  inner <- local (_ { indent = 4 }) (asks _.indent)
  { indent } <- ask
  pure (name <> show indent <> show inner)

logged :: Int -> Writer (Array String) Int
logged n = do
  tell [ "start " <> show n ]
  traverse_ (\i -> tell [ show i ]) (Array.range 1 n)
  pure (n * n)

main :: Effect Unit
main = do
  log (sameAndBigger 1 1 <> sameAndBigger "b" "a" <> sameAndBigger [ 1 ] [ 1, 2 ] <> sameAndBigger (Just 1.5) Nothing)
  log (summarize [ 3, 1, 2 ] <> " | " <> summarize [ "x", "y" ] <> " | " <> summarize ([] :: Array Boolean) <> " | " <> summarize [ Just 'a', Nothing ])
  log (applyToBoth show (1 /\ "s"))
  let tree = Rose 1 [ Rose 2 [ Rose 4 [] ], Rose 3 [] ]
  log (show (tree <#> (_ * 10)))
  log (show (Array.fromFoldable tree) <> show (foldr Array.cons [] tree) <> show (foldl (flip Array.cons) [] tree) <> foldMap show tree)
  log (show (traverse (\n -> if n > 0 then Just (n - 1) else Nothing) tree))
  log (show (traverse (\n -> if n > 3 then Left n else Right n) tree))
  log (show (sequence [ Just 1, Just 2 ]) <> show (sequence [ Just 1, Nothing ]))
  log (show (evalState (labelTree (tree <#> show)) 100))
  log (show (runState counter 5))
  log (runReader configured { indent: 2, name: "cfg" })
  log (show (runWriter (logged 3)))
  log (show (restock [ 1, 2, 3 ]) <> show (restock tree) <> show (items (shelve 'q' :: Rose Char)))
  log (either show (_ <> "!") (Right "ok" :: Either Int String) <> either show (_ <> "!") (Left 4 :: Either Int String))
  where
  cons' = Array.cons
