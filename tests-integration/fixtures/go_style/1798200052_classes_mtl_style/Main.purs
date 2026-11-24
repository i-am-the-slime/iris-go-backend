module T.Mtl where

import Prelude

import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Reader (ReaderT, runReaderT, asks)
import Control.Monad.State (class MonadState, StateT, get, modify_, runStateT, gets)
import Control.Monad.Writer (class MonadTell, WriterT, runWriterT, tell)
import Control.Monad.Error.Class (class MonadThrow)
import Control.Monad.Reader.Class (class MonadAsk)
import Data.Array as Array
import Data.Either (Either)
import Data.Functor.Compose (Compose(..))
import Data.Identity (Identity(..))
import Data.Maybe (Maybe(..))
import Data.Newtype (un)
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Console (log)

-- own class with fundep over a monad
class Monad m <= MonadLogger m where
  logLine :: String -> m Unit

type App = ReaderT { limit :: Int } (StateT Int (WriterT (Array String) (ExceptT String Effect)))

instance MonadLogger Effect where
  logLine = log

step :: forall m. MonadAsk { limit :: Int } m => MonadState Int m => MonadTell (Array String) m => MonadThrow String m => Int -> m Unit
step amount = do
  limit <- asks _.limit
  modify_ (_ + amount)
  current <- get
  tell [ "added " <> show amount <> " -> " <> show current ]
  when (current > limit) (throwError ("over limit at " <> show current))

program :: forall m. MonadAsk { limit :: Int } m => MonadState Int m => MonadTell (Array String) m => MonadThrow String m => MonadEffect m => m String
program = do
  step 3
  step 4
  liftEffect (log "midway")
  doubled <- gets (_ * 2)
  pure ("doubled " <> show doubled)

runApp :: forall a. Int -> App a -> Effect (Either String ((a /\ Int) /\ Array String))
runApp limit app = app # flip runReaderT { limit } # flip runStateT 0 # runWriterT # runExceptT

main :: Effect Unit
main = do
  okResult <- runApp 100 program
  log (show okResult)
  badResult <- runApp 5 program
  log (show badResult)
  logLine "via own class"
  let composed = Compose [ Just 1, Nothing, Just 3 ]
  log (show (map (_ * 2) composed))
  log (show (un Identity (Identity 5 >>= \n -> pure (n + 1))))
  log (show (Array.foldMap (\n -> [ n, n ]) [ 1, 2 ]))
