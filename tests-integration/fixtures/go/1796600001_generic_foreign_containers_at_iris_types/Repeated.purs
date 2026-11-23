module Repeated where

import Data.Function.Uncurried (Fn2, Fn3)

foreign import data Repeated :: Type -> Type

foreign import empty :: forall a. Repeated a

foreign import snocImpl :: forall a. Fn2 (Repeated a) a (Repeated a)

foreign import freeze :: forall a. Repeated a -> Array a

foreign import length :: forall a. Repeated a -> Int

foreign import indexOrImpl :: forall a. Fn3 a Int (Repeated a) a

foreign import describe :: forall a. a -> String
