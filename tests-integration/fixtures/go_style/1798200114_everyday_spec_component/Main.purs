module Spec.Component where

import Prelude

import Effect (Effect)
import Effect.Console (log)
import Effect.Ref as Ref
import Data.Variant as Variant
import Type.Proxy (Proxy(..))

newtype Action a = Action (Effect a)

runAction :: forall a. Action a -> Effect a
runAction (Action effect) = effect

instance Functor Action where
  map change (Action effect) = Action (map change effect)

instance Apply Action where
  apply = ap

instance Applicative Action where
  pure = Action <<< pure

instance Bind Action where
  bind (Action effect) next = Action (effect >>= (next >>> runAction))

instance Monad Action

newtype Hooks a = Hooks (Effect a)

runHooks :: forall a. Hooks a -> Effect a
runHooks (Hooks effect) = effect

type Self props message =
  { props :: Action props
  , emit :: message -> Action Unit
  }

newtype Component props message = Component (Self props message -> Hooks (Action String))

component :: forall props message. (Self props message -> Hooks (Action String)) -> Component props message
component = Component

mount :: forall props message. Component props message -> props -> (message -> Action Unit) -> Hooks (Action String)
mount (Component render) props handle = render { props: pure props, emit: handle }

type Todo = { title :: String, done :: Boolean }

data TodoMessage = Toggle | Delete

todoItem = component \{ props, emit } -> Hooks do
  pure do
    todo <- props <#> _.todo
    emit Toggle
    pure (todo.title <> if todo.done then " [x]" else " [ ]")

titleOnly = component \{ props } -> Hooks do
  pure (props <#> _.label)

clicker = component \{ props, emit } -> Hooks do
  pure do
    count <- props <#> _.count
    emit (Variant.inj (Proxy :: Proxy "clicked") count)
    pure ("clicked " <> show count)

main :: Effect Unit
main = do
  toggles <- Ref.new 0
  let handle = case _ of
        Toggle -> Ref.modify_ (_ + 1) toggles # Action
        Delete -> pure unit
  view <- runHooks (mount todoItem { todo: { title: "write tests", done: false }, selected: true } handle)
  runAction view >>= log
  runAction view >>= log
  label <- runHooks (mount titleOnly { label: "header", width: 80 } (\_ -> pure unit))
  runAction label >>= log
  clicks <- runHooks (mount clicker { count: 3 } (\_ -> pure unit))
  runAction clicks >>= log
  Ref.read toggles <#> show >>= log
