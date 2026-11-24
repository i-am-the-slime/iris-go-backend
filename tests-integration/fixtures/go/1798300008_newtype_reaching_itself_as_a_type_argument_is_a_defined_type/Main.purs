module Main where

import Prelude

import Data.Foldable (for_)
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Journal (log)

newtype Action a = Action (Env -> Effect a)

type Env = { listeners :: Ref (Array (Action Unit)) }

runAction :: forall a. Env -> Action a -> Effect a
runAction env (Action run) = run env

listen :: Action Unit -> Action Unit
listen listener = Action \env -> Ref.modify_ (_ <> [ listener ]) env.listeners

say :: String -> Action Unit
say text = Action \_ -> log text

main :: Effect Unit
main = do
  listeners <- Ref.new []
  let env = { listeners }
  runAction env (listen (say "first"))
  runAction env (listen (say "second"))
  heard <- Ref.read listeners
  for_ heard (runAction env)
