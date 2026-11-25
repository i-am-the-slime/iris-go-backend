module Journal (log) where

import Prelude

import Effect (Effect)

foreign import log :: String -> Effect Unit
