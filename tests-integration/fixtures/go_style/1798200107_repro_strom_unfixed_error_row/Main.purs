module Repro.R01 where

import Prelude

import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.Except (ExceptT, runExceptT)
import Data.Either (Either, either)
import Data.Variant (Variant, inj)
import Effect (Effect)
import Effect.Console (log)
import Effect.Exception (Error, error)
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
  | n < 0 = throwError (inj (Proxy :: Proxy "exception") (error "negative"))
  | otherwise = pure (n + 1)

main :: Effect Unit
main = do
  result <- runThrower (guarded 41)
  log (either (const "failed") show result)
