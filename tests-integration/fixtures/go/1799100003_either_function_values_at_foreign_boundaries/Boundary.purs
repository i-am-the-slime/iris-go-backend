module Boundary (keepImpl, repeatImpl) where

import Effect (Effect)

foreign import repeatImpl :: forall a. Int -> Effect a -> Effect (Array a)

foreign import keepImpl :: forall a. a -> Effect a
