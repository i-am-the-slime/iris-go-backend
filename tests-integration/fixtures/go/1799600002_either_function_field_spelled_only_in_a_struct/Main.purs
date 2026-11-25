module Main where

import Prelude

import Data.Either (Either)
import Effect (Effect)
import Journal (log)

data ReadError = Unknown String | Empty

newtype Reader a = Reader { name :: String, read :: String -> Either ReadError a }

data Parser a
  = Option (Reader a)
  | Done a
  | Both (Parser a) (Parser a)

names :: forall a. Parser a -> Array String
names = case _ of
  Option (Reader reader) -> [ reader.name ]
  Done _ -> []
  Both left right -> names left <> names right

main :: Effect Unit
main = do
  log (show (names (Both (Done 1) (Done 2))))
  log (show (names (Done "a")))
