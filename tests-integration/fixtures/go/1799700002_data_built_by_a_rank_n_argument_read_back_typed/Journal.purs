module Journal (count, log) where

import Prelude

import Effect (Effect)

foreign import count :: Effect Int

foreign import log :: String -> Effect Unit
