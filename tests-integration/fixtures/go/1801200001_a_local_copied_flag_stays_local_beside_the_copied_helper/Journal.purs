module Journal (log, positions) where

import Prelude

import Effect (Effect)

foreign import log :: String -> Effect Unit

foreign import positions :: Array Int
