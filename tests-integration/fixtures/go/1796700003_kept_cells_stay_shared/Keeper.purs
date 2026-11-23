module Keeper where

import Effect (Effect)

foreign import keep :: forall a. a -> Int

foreign import kept :: forall a. Effect a
