module Clock where

import Effect (Effect)

foreign import now :: Effect Number
foreign import elapsed :: Number -> Effect Number
