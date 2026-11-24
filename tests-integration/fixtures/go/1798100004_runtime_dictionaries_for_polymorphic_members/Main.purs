module Main where

import Prelude

import Data.Foldable (class Foldable, foldMap, foldl, foldr, length, sum)
import Data.Maybe (Maybe(..))
import Data.Traversable (class Traversable, traverse)
import Effect.Unsafe (unsafePerformEffect)

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

counted :: forall f. Foldable f => Int -> f Int -> Int
counted 0 values = length values + sum values
counted depth values = counted (depth - 1) (Wrapped values)

described :: forall f. Foldable f => Int -> f Int -> String
described 0 values = foldMap show values
described depth values = described (depth - 1) (Wrapped values)

doubled :: forall f. Functor f => Foldable f => Int -> f Int -> Int
doubled 0 values = sum (values <#> (_ * 2))
doubled depth values = doubled (depth - 1) (Wrapped values)

checked :: forall f. Traversable f => Int -> f Int -> Maybe Int
checked 0 values = values # traverse (\n -> if n > 0 then Just n else Nothing) <#> sum
checked depth values = checked (depth - 1) (Wrapped values)

stepped :: forall m. Monad m => Int -> m Int -> m Int
stepped 0 action = do
  n <- action
  m <- pure (n * 10)
  pure (m + 1)
stepped depth action = unlift (stepped (depth - 1) (Lift action))

main :: Array String
main =
  [ show (counted 3 [ 1, 2 ])
  , described 2 [ 4, 5, 6 ]
  , show (doubled 4 [ 1, 2, 3 ])
  , show (checked 2 [ 1, 2 ]) <> " " <> show (checked 2 [ 1, 0 ])
  , show (unsafePerformEffect (stepped 3 (pure 4)))
  , show (stepped 2 (Just 5))
  ]
