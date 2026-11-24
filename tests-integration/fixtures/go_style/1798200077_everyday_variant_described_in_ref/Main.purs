module Fix.F2 where

import Prelude

import Data.Foldable (traverse_)
import Data.Variant as Variant
import Effect (Effect)
import Effect.Console (log)
import Effect.Ref as Ref
import Effect.Unsafe (unsafePerformEffect)
import Type.Proxy (Proxy(..))

data Box :: Row Type -> Type
data Box row = Box

class Labelled :: Type -> Type -> Constraint
class Labelled payload box | box -> payload where
  label :: Proxy box -> String

instance Labelled (Record (tag :: Int | row)) (Box row) where
  label _ = "box"

describe :: forall row. Labelled (Record (tag :: Int | row)) (Box row) => Box row -> String
describe _ = label (Proxy :: Proxy (Box row))

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

type Self props message =
  { props :: Action props
  , emit :: message -> Action Unit
  }

newtype Component props message = Component (Self props message -> Action String)

component :: forall props message. (Self props message -> Action String) -> Component props message
component = Component

mount :: forall props message. Component props message -> props -> (message -> Action Unit) -> Action String
mount (Component render) props handle = render { props: pure props, emit: handle }

data TodoMessage = Toggle | Delete

todoItem = component \{ props, emit } -> do
  todo <- props <#> _.todo
  emit Toggle
  pure (todo.title <> if todo.done then " [x]" else " [ ]")

clicker = component \{ props, emit } -> do
  count <- props <#> _.count
  emit (Variant.inj (Proxy :: Proxy "clicked") count)
  pure ("clicked " <> show count)

mounted :: Effect (Array String)
mounted = do
  toggles <- Ref.new 0
  let
    handle = case _ of
      Toggle -> Ref.modify_ (_ + 1) toggles # Action
      Delete -> pure unit
  item <- mount todoItem { todo: { title: "write tests", done: false }, selected: true } handle # runAction
  clicks <- mount clicker { count: 3 } (\_ -> pure unit) # runAction
  toggled <- Ref.read toggles
  pure [ item, clicks, show toggled ]

main :: Effect Unit
main = results # traverse_ log

results :: Array String
results = [ describe Box ] <> unsafePerformEffect mounted
