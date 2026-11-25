module Main where

import Prelude

import Data.Either (Either(..))
import Data.Exists (Exists, mkExists, runExists)
import Effect (Effect)
import Journal (log)

newtype Reader a = Reader (String -> Either String a)

data Parser a
  = Option (Reader a)
  | Done a
  | Apply (Exists (Applied a))

data Applied a x = Applied (Parser (x -> a)) (Parser x)

instance Functor Parser where
  map f = case _ of
    Option (Reader read) -> Option (Reader (map f <<< read))
    Done a -> Done (f a)
    Apply applied -> runExists (\(Applied function argument) -> Apply (mkExists (Applied (map (f <<< _) function) argument))) applied

instance Apply Parser where
  apply function argument = Apply (mkExists (Applied function argument))

parse :: forall a. Parser a -> String -> Either String a
parse parser word = case parser of
  Option (Reader read) -> read word
  Done a -> Right a
  Apply applied -> runExists (\(Applied function argument) -> parse function word <*> parse argument word) applied

data Command = Hello | Bye

instance Show Command where
  show Hello = "hello"
  show Bye = "bye"

modifier :: Parser (Command -> Command)
modifier = Option (Reader (\_ -> Right identity))

main :: Effect Unit
main = log (show (parse ((>>>) <$> modifier <*> modifier <*> Done Bye) "x"))
