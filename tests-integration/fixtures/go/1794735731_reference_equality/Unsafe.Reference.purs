module Unsafe.Reference where

foreign import reallyUnsafeRefEq :: forall a b. a -> b -> Boolean

unsafeRefEq :: forall a. a -> a -> Boolean
unsafeRefEq = reallyUnsafeRefEq
