module T.RecB where

import Prelude

import Data.Array as Array
import Data.Foldable (class Foldable, foldMap, foldl, foldr, intercalate)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Console (log)

data Rose a = Rose a (Array (Rose a))

instance Functor Rose where
  map f (Rose a kids) = Rose (f a) (kids <#> map f)

instance Show a => Show (Rose a) where
  show (Rose a kids) = "R" <> show a <> show kids

tree :: Rose Int
tree = Rose 1 [ Rose 2 [ Rose 4 [] ], Rose 3 [] ]

main :: Effect Unit
main = do
  log (show (map (_ + 1) tree))
  log (show (tree <#> (_ * 2) <#> show))
  log (show (tree <#> (_ * 2) <#> (_ + 1) <#> show))
  log (show ((_ + 1) <$> tree))
