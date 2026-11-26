module Cell (Cell, new, read, write) where

import Effect (Effect)
import Prelude (Unit)

foreign import data Cell :: Type -> Type

foreign import new :: forall a. a -> Effect (Cell a)
foreign import read :: forall a. Cell a -> Effect a
foreign import write :: forall a. Cell a -> a -> Effect Unit
