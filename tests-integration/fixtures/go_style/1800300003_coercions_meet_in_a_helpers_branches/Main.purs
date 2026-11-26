module Main where

import Prelude

import Control.Monad.State (State, execState, modify_)
import Data.Maybe (Maybe(..), isJust)
import Data.TraversableWithIndex (forWithIndex)
import Data.Void (Void)
import Effect (Effect)
import Effect.Console (log, logShow)
import Unsafe.Coerce (unsafeCoerce)

type Steps = { before :: Maybe Void, each :: Maybe Void }

newtype Plan :: Type -> Type -> Type -> Type
newtype Plan a b x = Plan (State Steps x)

derive newtype instance Functor (Plan a b)
derive newtype instance Apply (Plan a b)
derive newtype instance Applicative (Plan a b)
derive newtype instance Bind (Plan a b)
derive newtype instance Monad (Plan a b)

before :: forall a b. (a -> Effect Unit) -> Plan a b Unit
before f = Plan (modify_ _ { before = Just (unsafeCoerce f) })

each :: forall a b. (a -> Effect b) -> Plan a b Unit
each f = Plan (modify_ _ { each = Just (unsafeCoerce f) })

prepared :: forall a. Maybe Void -> (a -> Effect Unit)
prepared step = case step of
  Nothing -> \_ -> pure unit
  Just f -> unsafeCoerce f

runPlan :: forall a b. Array a -> Plan a b Unit -> Effect (Array b)
runPlan items (Plan plan) = do
  let steps = execState plan { before: Nothing, each: Nothing }
  results <- forWithIndex items \_ item -> do
    let before' = unsafeCoerce (prepared steps.before) :: a -> Effect Unit
    let each' = unsafeCoerce (prepared steps.each) :: a -> Effect b
    before' item
    each' item
  pure (if isJust steps.each then results else [])

main :: Effect Unit
main = do
  labels <- runPlan [ 1, 2 ] do
    before \n -> log ("before " <> show n)
    each \n -> pure ("item " <> show (n * 10))
  logShow labels
  skipped <- runPlan [ 3 ] (before \n -> log ("only before " <> show n))
  logShow (skipped :: Array String)
