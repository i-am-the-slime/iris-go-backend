module Main where

import Prelude

import Unsafe.Coerce (unsafeCoerce)

-- `(f ~> State s) -> Free f ~> State s` binds the synonym's `a` twice. The
-- interpreter `k` stays polymorphic; it is used at the existential `Val`,
-- not at the program's result type. `hoistFree k`'s body has the type
-- `Free f ~> Free g`, instantiated at the program's result type, while the
-- argument it passes to `substFree` stays polymorphic.

data Val

data Free f a = Pure a | Bind (f Val) (Val -> Free f a)

newtype State s a = State (s -> { value :: a, state :: s })

data Command next = Push Int next | Pop (Int -> next)

data Instruction next = Store Int next | Load (Int -> next)

liftF :: forall f a. f a -> Free f a
liftF command = Bind (unsafeCoerce command) (\value -> Pure (unsafeCoerce value))

andThen :: forall f a b. Free f a -> (a -> Free f b) -> Free f b
andThen program next = case program of
  Pure a -> next a
  Bind command continue -> Bind command (\value -> andThen (continue value) next)

substFree :: forall f g. (f ~> Free g) -> Free f ~> Free g
substFree k = case _ of
  Pure a -> Pure a
  Bind command continue -> k command `andThen` \value -> substFree k (continue value)

hoistFree :: forall f g. (f ~> g) -> Free f ~> Free g
hoistFree k = substFree (liftF <<< k)

toCommand :: Instruction ~> Command
toCommand = case _ of
  Store value next -> Push value next
  Load continue -> Pop continue

runState :: forall s a. State s a -> s -> { value :: a, state :: s }
runState (State run) = run

foldFree :: forall f s. (f ~> State s) -> Free f ~> State s
foldFree k program = State \state -> case program of
  Pure a -> { value: a, state }
  Bind command continue -> do
    let result = runState (k command) state
    runState (foldFree k (continue result.value)) result.state

intoState :: Command ~> State Int
intoState = case _ of
  Push value next -> State \_ -> { value: next, state: value }
  Pop continue -> State \state -> { value: continue state, state }

program :: Free Command Int
program = liftF (Push 41 unit) `andThen` \_ -> liftF (Pop identity)

instructions :: Free Instruction Int
instructions = liftF (Store 6 unit) `andThen` \_ -> liftF (Load (_ * 7))

main :: Array Int
main =
  [ (runState (foldFree intoState program) 0).value + 1
  , (runState (foldFree intoState (hoistFree toCommand instructions)) 0).value
  ]
