module Fix.F1 where

import Prelude

import Data.Foldable (class Foldable, foldMap, foldl, foldr, traverse_)
import Data.Maybe (Maybe(..))
import Data.Traversable (class Traversable, for, traverse)
import Effect (Effect)
import Effect.Console (log)
import Effect.Unsafe (unsafePerformEffect)

data Rose a = Rose a (Array (Rose a))

mapOver :: forall f a b. Functor f => f a -> (a -> b) -> f b
mapOver container change = map change container

instance Functor Rose where
  map change (Rose value kids) = Rose (change value) (mapOver kids (map change))

instance Foldable Rose where
  foldr step initial (Rose value kids) = step value (foldr (\kid rest -> foldr step rest kid) initial kids)
  foldl step initial (Rose value kids) = foldl (\rest kid -> foldl step rest kid) (step initial value) kids
  foldMap visit (Rose value kids) = visit value <> foldMap (foldMap visit) kids

instance Traversable Rose where
  traverse visit (Rose value kids) = Rose <$> visit value <*> for kids (traverse visit)
  sequence = traverse identity

newtype Task a = Task (Effect a)

runTask :: forall a. Task a -> Effect a
runTask (Task effect) = effect

instance Functor Task where
  map change (Task effect) = Task (map change effect)

instance Apply Task where
  apply = ap

instance Applicative Task where
  pure = Task <<< pure

instance Bind Task where
  bind (Task effect) next = Task (map next effect >>= runTask)

instance Monad Task

tree :: Rose Int
tree = Rose 1 [ Rose 2 [], Rose 3 [ Rose 4 [] ] ]

main :: Effect Unit
main = results # traverse_ log

results :: Array String
results =
  [ for tree (\n -> Just n) <#> foldl (+) 0 # show
  , mapOver tree (_ * 10) # foldMap (\n -> show n <> ";")
  , (+) <$> pure 1 <*> pure 2 # runTask # unsafePerformEffect # show
  ]
