module Go.IO.Internal (catchImpl) where

import Effect (Effect)
import Effect.Exception (Error)

foreign import catchImpl :: forall a. (Error -> Effect a) -> Effect a -> Effect a
