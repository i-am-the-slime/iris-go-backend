module Compat.Effects.Run where

import Prelude

import Data.Either (Either(..))
import Data.Tuple.Nested ((/\))
import Run (Run, EFFECT, interpret, lift, on, send, extract, runBaseEffect, liftEffect)
import Run.Except (EXCEPT, runExcept, throw, catch)
import Run.Reader (READER, ask, local, runReader)
import Run.State (STATE, get, modify, put, runState)
import Run.Writer (WRITER, tell, runWriter)
import Effect (Effect)
import Effect.Console (log)
import Type.Proxy (Proxy(..))
import Type.Row (type (+))

data TalkF a = Speak String a | Listen (String -> a)

derive instance Functor TalkF

type TALK r = (talk :: TalkF | r)

_talk = Proxy :: Proxy "talk"

speak :: forall r. String -> Run (TALK + r) Unit
speak message = lift _talk (Speak message unit)

listen :: forall r. Run (TALK + r) String
listen = lift _talk (Listen identity)

program :: forall r. Run (TALK + STATE Int + READER String + EXCEPT String + WRITER (Array String) + r) Int
program = do
  greeting <- ask
  speak greeting
  name <- listen
  tell [ "heard " <> name ]
  modify (_ + 10)
  count <- get
  when (count > 100) (throw "too many")
  scoped <- local (_ <> "!") ask
  speak scoped
  recovered <- catch (\error -> pure ("recovered " <> error)) (throw "boom")
  tell [ recovered ]
  put (count * 2)
  pure (count + 1)

runTalk :: forall r. Run (TALK + EFFECT + r) ~> Run (EFFECT + r)
runTalk = interpret (on _talk handle send)
  where
  handle :: TalkF ~> Run (EFFECT + r)
  handle (Speak message next) = do
    liftEffect (log ("speak: " <> message))
    pure next
  handle (Listen reply) = pure (reply "world")

main :: Effect Unit
main = do
  result <- program
    # runReader "hello"
    # runState 5
    # runExcept
    # runWriter
    # runTalk
    # runBaseEffect
  case result of
    logs /\ Right (state /\ value) -> log ("state " <> show state <> " value " <> show value <> " logs " <> show logs)
    logs /\ Left error -> log ("error " <> error <> " logs " <> show logs)
  log (show (extract (runState 0 (modify (_ + 1) *> get :: Run (STATE Int ()) Int))))
