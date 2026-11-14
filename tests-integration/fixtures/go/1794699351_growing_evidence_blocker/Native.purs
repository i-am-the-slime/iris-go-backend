module Native where

import Prelude

foreign import describe :: forall a. Show a => a -> String
