module Fun.Wrappers where

import Prelude

import Data.Functor.Compose (Compose(..))
import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Newtype (un)
import Effect (Effect)
import Effect.Console (log)

newtype Wrap f a = Wrap (f a)

unwrapped :: forall f a. Wrap f a -> f a
unwrapped (Wrap inner) = inner

instance Functor f => Functor (Wrap f) where
  map g (Wrap inner) = Wrap (inner <#> g)

newtype Dollar f a = Dollar (f a)

instance Functor f => Functor (Dollar f) where
  map g (Dollar inner) = Dollar (g <$> inner)

newtype Derived f a = Derived (f a)

derive instance Functor f => Functor (Derived f)

newtype Twice f a = Twice (f (f a))

instance Functor f => Functor (Twice f) where
  map g (Twice inner) = Twice (map (map g) inner)

data Pair a = Pair a a

instance Functor Pair where
  map f (Pair a b) = Pair (a # f) (b # f)

instance Show a => Show (Pair a) where
  show (Pair a b) = "<" <> show a <> "," <> show b <> ">"

data Rose a = Rose a (Array (Rose a))

instance Functor Rose where
  map f (Rose label children) = Rose (f label) (map (map f) children)

instance Show a => Show (Rose a) where
  show (Rose label children) = "Rose " <> show label <> show children

data Free f a = Pure a | Roll (f (Free f a))

instance Functor f => Functor (Free f) where
  map f (Pure a) = Pure (f a)
  map f (Roll layer) = Roll (map (map f) layer)

collapse :: forall a. Free Pair a -> Array a
collapse (Pure a) = [ a ]
collapse (Roll (Pair left right)) = collapse left <> collapse right

newtype Task a = Task (Effect a)

runTask :: forall a. Task a -> Effect a
runTask (Task effect) = effect

instance Functor Task where
  map f (Task effect) = Task (effect <#> f)

instance Apply Task where
  apply (Task ef) (Task ea) = Task (ef <*> ea)

instance Applicative Task where
  pure = Task <<< pure

instance Bind Task where
  bind (Task effect) next = Task (effect >>= (next >>> runTask))

instance Monad Task

main :: Effect Unit
main = do
  let wrapped = Wrap [ 1, 2, 3 ]
  log $ show (unwrapped (wrapped <#> (_ + 1) <#> (_ * 2) <#> show <#> (_ <> "!") <#> (_ <> "?")))
  log $ show (unwrapped (map (_ <> "?") (map (_ <> "!") (map show (map (_ * 2) (map (_ + 1) wrapped))))))
  log $ show (unwrapped (unwrapped (Wrap (Wrap (Just 4)) <#> (_ + 1) <#> show)))
  log $ show (unwrapped (unwrapped (Wrap (Wrap [ 1 ]) <#> (_ + 1) <#> show)))
  log $ show (case Dollar (Right 5 :: Either String Int) <#> (_ + 1) <#> (_ * 3) of Dollar inner -> inner)
  log $ show (case Derived (Just 5) <#> (_ + 1) <#> (_ * 3) <#> show of Derived inner -> inner)
  log $ show (case Twice [ [ 1, 2 ], [ 3 ] ] <#> (_ + 1) <#> (_ * 3) <#> show of Twice inner -> inner)
  log $ show (case Twice (Just (Just 1)) <#> (_ + 1) <#> show of Twice inner -> inner)
  log $ show (Pair 1 2 <#> (_ + 1) <#> (_ * 2) <#> show)
  log $ show (Compose (Pair (Just 1) Nothing) <#> (_ + 1) <#> show)
  log $ show (map show (map (_ + 1) (Compose (Wrap [ Pair 1 2 ]))) # un Compose # unwrapped)
  log $ show (Rose 1 [ Rose 2 [], Rose 3 [ Rose 4 [] ] ] <#> (_ * 10) <#> (_ + 1) <#> show)
  log $ show (collapse (Roll (Pair (Pure 1) (Roll (Pair (Pure 2) (Pure 3)))) <#> (_ * 10) <#> (_ + 1)))
  taskResult <- runTask ((+) <$> pure 1 <*> pure 2 <#> (_ * 10))
  log $ show taskResult
  taskDo <- runTask do
    a <- pure 1
    b <- Task (pure 2) <#> (_ + 1)
    pure (a + b)
  log $ show taskDo
