module Buffers where

import Unsafe.Coerce (unsafeCoerce)

foreign import data Mutable :: Type
foreign import data Frozen :: Type

foreign import new :: Int -> Mutable
foreign import size :: Frozen -> Int

freeze :: Mutable -> Frozen
freeze = unsafeCoerce
