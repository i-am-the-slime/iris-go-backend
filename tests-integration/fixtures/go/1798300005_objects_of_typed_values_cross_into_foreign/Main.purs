module Main where

import Prelude

import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Console (log)
import Foreign (Foreign, typeOf, unsafeFromForeign, unsafeToForeign)
import Foreign.Object (Object)
import Foreign.Object as Object
import Yoga.JSON (unsafeStringify)

main :: Effect Unit
main = do
  log (typeOf schemes)
  log (unsafeStringify schemes)
  log (show (Object.lookup "apiKey" (unsafeFromForeign schemes :: Object Int)))
  where
  schemes :: Foreign
  schemes = unsafeToForeign (Object.fromFoldable [ "bearerAuth" /\ 1, "apiKey" /\ 2 ])
