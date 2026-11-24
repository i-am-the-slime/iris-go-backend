module Main where

import Prelude

import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Foreign (Foreign, typeOf, unsafeFromForeign, unsafeToForeign)
import Foreign.Object (Object)
import Foreign.Object as Object
import Journal (log)
import Yoga.JSON (unsafeStringify)

main :: Effect Unit
main = do
  log (typeOf schemes)
  log (unsafeStringify schemes)
  log (show (Object.lookup "apiKey" (unsafeFromForeign schemes :: Object Int)))
  where
  schemes :: Foreign
  schemes = unsafeToForeign (Object.fromFoldable [ "bearerAuth" /\ 1, "apiKey" /\ 2 ])
