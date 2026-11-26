module Main where

import Prelude

import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.Except (ExceptT, runExceptT)
import Data.Either (Either, either)
import Data.Variant (Variant, default, inj, on)
import Effect (Effect)
import Effect.Exception (Error, error, message)
import Type.Proxy (Proxy(..))

newtype Thrower err a = Thrower (ExceptT (Variant (exception :: Error | err)) Effect a)

derive newtype instance Functor (Thrower err)
derive newtype instance Apply (Thrower err)
derive newtype instance Applicative (Thrower err)
derive newtype instance Bind (Thrower err)
derive newtype instance Monad (Thrower err)
derive newtype instance MonadThrow (Variant (exception :: Error | err)) (Thrower err)

runThrower :: forall err a. Thrower err a -> Effect (Either (Variant (exception :: Error | err)) a)
runThrower (Thrower action) = runExceptT action

guarded :: forall m err. MonadThrow (Variant (exception :: Error | err)) m => Int -> m Int
guarded n
  | n < 0 = throwError (inj exception (error "negative"))
  | otherwise = pure (n + 1)

taken :: Thrower (nameTaken :: String, invalidArgument :: String) Int
taken = throwError (inj nameTaken "ada")

main :: Effect (Array String)
main = do
  handled <- runThrower taken
  looped <- runThrower (guarded (-1))
  pure [ either explained show handled, either (default "unexpected" # on exception message) show looped ]
  where
  explained = default "unexpected"
    # on exception message
    # on nameTaken (\name -> name <> " is taken")

exception :: Proxy "exception"
exception = Proxy

nameTaken :: Proxy "nameTaken"
nameTaken = Proxy
