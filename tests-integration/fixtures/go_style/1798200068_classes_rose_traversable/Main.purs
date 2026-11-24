module T.RecK where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Traversable (class Traversable, for, traverse, sequence)
import Data.Foldable (class Foldable, foldMap, foldl, foldr)
import Effect (Effect)
import Effect.Console (log)

data Rose a = Rose a (Array (Rose a))

relabel :: forall a b. (a -> b) -> Rose a -> Rose b
relabel f (Rose a kids) = Rose (f a) (kids <#> relabel f)

instance Functor Rose where
  map f (Rose a kids) = Rose (f a) (map (map f) kids)
instance Foldable Rose where
  foldr f z (Rose a kids) = f a (foldr (\kid acc -> foldr f acc kid) z kids)
  foldl f z (Rose a kids) = foldl (\acc kid -> foldl f acc kid) (f z a) kids
  foldMap f (Rose a kids) = f a <> foldMap (foldMap f) kids
instance Traversable Rose where
  traverse f (Rose a kids) = Rose <$> f a <*> for kids (traverse f)
  sequence = traverse identity

instance Show a => Show (Rose a) where
  show (Rose a kids) = "R" <> show a <> show kids

main :: Effect Unit
main = do
  let tree = Rose 1 [ Rose 2 [ Rose 4 [] ], Rose 3 [] ]
  log (show (relabel show tree))
  log (show (relabel (_ + 1) tree <#> (_ * 2)))
  log (show (traverse (\n -> if n > 0 then Just n else Nothing) tree))
  log (show (for tree (\n -> [ n, -n ]) # map (foldl (+) 0)))
