module Spec.Fallback where

import Prelude

import Data.Foldable (class Foldable, foldMap, foldl, foldr, length, sum)
import Data.Maybe (Maybe(..))
import Data.Traversable (class Traversable, traverse, sequence)
import Effect (Effect)
import Effect.Console (log)

data Wrapped f a = Wrapped (f a)

instance Functor f => Functor (Wrapped f) where
  map change (Wrapped inner) = Wrapped (inner <#> change)

instance Foldable f => Foldable (Wrapped f) where
  foldr step initial (Wrapped inner) = foldr step initial inner
  foldl step initial (Wrapped inner) = foldl step initial inner
  foldMap visit (Wrapped inner) = foldMap visit inner

instance Traversable f => Traversable (Wrapped f) where
  traverse visit (Wrapped inner) = Wrapped <$> traverse visit inner
  sequence = traverse identity

count :: forall f. Foldable f => Int -> f Int -> Int
count 0 values = length values + sum values
count depth values = count (depth - 1) (Wrapped values)

describe :: forall f. Foldable f => Int -> f Int -> String
describe 0 values = foldMap show values
describe depth values = describe (depth - 1) (Wrapped values)

doubled :: forall f. Functor f => Foldable f => Int -> f Int -> Int
doubled 0 values = sum (values <#> (_ * 2))
doubled depth values = doubled (depth - 1) (Wrapped values)

checked :: forall f. Traversable f => Int -> f Int -> Maybe Int
checked 0 values = values # traverse (\n -> if n > 0 then Just n else Nothing) <#> sum
checked depth values = checked (depth - 1) (Wrapped values)

wrappedShow :: forall a. Show a => Int -> a -> String
wrappedShow 0 value = show value
wrappedShow depth value = wrappedShow (depth - 1) [ value ]

newtype Lift m a = Lift (m a)

unlift :: forall m a. Lift m a -> m a
unlift (Lift inner) = inner

instance Functor m => Functor (Lift m) where
  map change (Lift inner) = Lift (inner <#> change)

instance Apply m => Apply (Lift m) where
  apply (Lift change) (Lift inner) = Lift (change <*> inner)

instance Applicative m => Applicative (Lift m) where
  pure = Lift <<< pure

instance Bind m => Bind (Lift m) where
  bind (Lift inner) next = Lift (inner >>= (next >>> unlift))

instance Monad m => Monad (Lift m)

stepped :: forall m. Monad m => Int -> m Int -> m Int
stepped 0 action = do
  n <- action
  m <- pure (n * 10)
  pure (m + 1)
stepped depth action = unlift (stepped (depth - 1) (Lift action))

related :: forall a. Ord a => Int -> a -> a -> String
related 0 left right = show (left == right) <> " " <> show (compare left right)
related depth left right = related (depth - 1) [ left ] [ right, right ]

main :: Effect Unit
main = do
  stepped 3 (pure 4) >>= show >>> log
  log (show (stepped 2 (Just 5)))
  log (related 2 1 1)
  log (show (count 3 [ 1, 2 ]))
  log (describe 2 [ 4, 5, 6 ])
  log (show (doubled 4 [ 1, 2, 3 ]))
  log (show (checked 2 [ 1, 2 ]) <> " " <> show (checked 2 [ 1, 0 ]))
  log (wrappedShow 3 'x')
