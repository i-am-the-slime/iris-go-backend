module Main where

import Prelude

import Control.Monad.Except (runExcept)
import Data.Either (Either(..))
import Effect (Effect)
import Effect.Ref as Ref
import Foreign (F, Foreign, readInt, unsafeToForeign)
import Journal (log)

described :: forall a. Show a => (Foreign -> F a) -> Foreign -> String
described read value = case runExcept (read value) of
  Right read' -> show read'
  Left errors -> "failed: " <> show errors

main :: Effect Unit
main = do
  reader <- Ref.new readInt >>= Ref.read
  log (described reader (unsafeToForeign 42))
  log (described reader (unsafeToForeign "forty-two"))
