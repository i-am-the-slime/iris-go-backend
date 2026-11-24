module Lifted where

import Effect (Effect)

newtype Action a = Action (Effect a)

foreign import performImpl :: forall a. Effect a -> Effect a

foreign import guardedImpl :: forall a. (String -> Action a) -> Action a -> Effect a

foreign import combineImpl :: forall a b c. (a -> b -> c) -> Effect a -> Effect b -> Effect c

foreign import modifyImpl :: forall t b. (Int -> t) -> (t -> b) -> Effect b
