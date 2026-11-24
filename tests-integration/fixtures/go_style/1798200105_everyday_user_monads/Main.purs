module Fun.UserMonads where

import Prelude

import Control.Apply (lift2)
import Data.Array ((..))
import Data.Traversable (traverse)
import Data.Tuple.Nested ((/\), type (/\))
import Effect (Effect)
import Effect.Aff (Aff, launchAff_)
import Effect.Class (liftEffect)
import Effect.Console (log)

newtype State s a = State (s -> a /\ s)

runState :: forall s a. State s a -> s -> a /\ s
runState (State run) = run

instance Functor (State s) where
  map = liftM1

instance Apply (State s) where
  apply = ap

instance Applicative (State s) where
  pure a = State \s -> a /\ s

instance Bind (State s) where
  bind (State run) next = State \s -> case run s of
    a /\ s' -> runState (next a) s'

instance Monad (State s)

modifyState :: forall s. (s -> s) -> State s s
modifyState f = State \s -> f s /\ f s

newtype App a = App (Int -> Aff a)

runApp :: forall a. Int -> App a -> Aff a
runApp env (App run) = run env

instance Functor App where
  map f (App run) = App \env -> run env <#> f

instance Apply App where
  apply = ap

instance Applicative App where
  pure a = App \_ -> pure a

instance Bind App where
  bind (App run) next = App \env -> run env >>= \a -> runApp env (next a)

instance Monad App

askEnv :: App Int
askEnv = App pure

main :: Effect Unit
main = do
  log $ show (runState (traverse (\n -> modifyState (_ + n)) (1 .. 5)) 0)
  log $ show (runState (lift2 (+) (modifyState (_ * 2)) (modifyState (_ + 1))) 5)
  log $ show (runState (modifyState (_ + 1) <#> (_ * 10) <#> show) 1)
  launchAff_ do
    result <- runApp 7 ((+) <$> askEnv <*> pure 1)
    log (show result) # liftEffect
