module Pipe (Pipe, newPipe, onTake, leaked) where

import Effect (Effect)
import Effect.Uncurried (EffectFn2)

foreign import data Pipe :: Type -> Type

foreign import newPipe :: forall a. a -> Pipe a

foreign import onTake :: forall a r. Pipe a -> EffectFn2 a Boolean r -> Effect r

-- | Its Go takes any pipe, so every Pipe holds boxed values.
foreign import leaked :: forall a. Pipe a -> Int
