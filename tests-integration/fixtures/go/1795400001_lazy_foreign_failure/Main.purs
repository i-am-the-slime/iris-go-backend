module Main where

import Prelude

import Control.Monad.Except (runExcept)
import Data.Either (Either, isLeft)
import Data.List.NonEmpty (NonEmptyList)
import Effect (Effect)
import Effect.Exception (throw)
import Foreign (Foreign, ForeignError, unsafeToForeign)
import Foreign.Index (readProp)

-- | `readProp`'s failure value, a `TypeMismatch` naming the value's `typeOf`, is built inside the
-- | closure `UnsafeReadPropImpl` calls when the read fails, not before every read.
property :: String -> Foreign -> Either (NonEmptyList ForeignError) Foreign
property key value = runExcept (readProp key value)

main :: Effect Unit
main = when (isLeft (property "name" (unsafeToForeign { name: "iris" }))) do
  throw "reading a present property fails"
