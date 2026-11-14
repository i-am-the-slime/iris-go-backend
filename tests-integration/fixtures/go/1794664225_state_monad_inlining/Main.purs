module Main where

import Prelude

newtype State s a = State (s -> { value :: a, state :: s })

runState :: forall s a. State s a -> s -> { value :: a, state :: s }
runState (State run) state = run state

bindState :: forall s a b. State s a -> (a -> State s b) -> State s b
bindState (State run) next = State \state ->
  let
    result = run state
    State continue = next result.value
  in
    continue result.state

pureState :: forall s a. a -> State s a
pureState value = State \state -> { value, state }

get :: forall s. State s s
get = State \state -> { value: state, state }

put :: forall s. s -> State s Unit
put state = State \_ -> { value: unit, state }

modify :: forall s. (s -> s) -> State s Unit
modify f = bindState get \state -> put (f state)

countDown :: Int -> State Int Unit
countDown 0 = pureState unit
countDown n = bindState (modify (_ + 1)) \_ -> countDown (n - 1)

main :: Int
main = (runState (countDown 60) 0).state
