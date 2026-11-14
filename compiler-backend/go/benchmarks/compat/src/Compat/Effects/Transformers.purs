module Compat.Effects.Transformers where

import Prelude

import Control.Monad.Except (ExceptT, runExceptT, throwError, catchError)
import Control.Monad.Reader (ReaderT, runReaderT, ask, asks, local)
import Control.Monad.State (StateT, runStateT, get, modify_, gets)
import Control.Monad.Writer (WriterT, runWriterT, tell)
import Control.Monad.Trans.Class (lift)
import Data.Either (Either(..))
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Aff (Aff, launchAff_, delay)
import Effect.Aff.Class (liftAff)
import Effect.Class (liftEffect)
import Effect.Console (log)
import Data.Time.Duration (Milliseconds(..))

type Config = { verbose :: Boolean, name :: String }

type App = ReaderT Config (StateT Int (WriterT (Array String) (ExceptT String Effect)))

step :: String -> App Unit
step label = do
  verbose <- asks _.verbose
  modify_ (_ + 1)
  n <- get
  when verbose (tell [ show n <> ":" <> label ])
  liftEffect (log ("effect " <> label))

app :: App String
app = do
  step "start"
  { name } <- ask
  local (_ { verbose = false }) (step "quiet")
  step name
  result <- catchError (step "risky" *> throwError "failed") (\e -> pure ("caught " <> e))
  count <- gets show
  pure (result <> " after " <> count)

type AffApp = StateT (Array Int) (ExceptT String Aff)

affApp :: AffApp Int
affApp = do
  modify_ (_ <> [ 1 ])
  lift (lift (delay (Milliseconds 1.0)))
  modify_ (_ <> [ 2 ])
  xs <- get
  when (xs == []) (throwError "empty")
  liftEffect (log ("aff state " <> show xs))
  pure 42

main :: Effect Unit
main = do
  outcome <- runExceptT (runWriterT (runStateT (runReaderT app { verbose: true, name: "main" }) 0))
  case outcome of
    Right ((value /\ state) /\ logs) -> log (value <> " state=" <> show state <> " logs=" <> show logs)
    Left error -> log ("error " <> error)
  launchAff_ do
    result <- runExceptT (runStateT affApp [])
    liftEffect (log (show result))
    _ <- liftAff (pure unit)
    pure unit
