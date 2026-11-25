module Main where

import Prelude

import Data.Either (Either(..))
import Data.Exists (Exists, mkExists, runExists)
import Effect (Effect)
import Journal (log)

data ReadError = Unknown String | Empty

instance Show ReadError where
  show (Unknown word) = "unknown " <> word
  show Empty = "empty"

newtype Reader a = Reader { name :: String, read :: String -> Either ReadError a }

data Parser a
  = Option (Reader a)
  | Done a
  | Apply (Exists (Applied a))

data Applied a x = Applied (Parser (x -> a)) (Parser x)

instance Functor Parser where
  map f parser = Apply (mkExists (Applied (Done f) parser))

instance Apply Parser where
  apply function argument = Apply (mkExists (Applied function argument))

instance Applicative Parser where
  pure = Done

parse :: forall a. Parser a -> String -> Either ReadError a
parse parser word = case parser of
  Option (Reader reader) -> reader.read word
  Done a -> Right a
  Apply applied -> runExists (\(Applied function argument) -> parse function word <*> parse argument word) applied

names :: forall a. Parser a -> Array String
names = case _ of
  Option (Reader reader) -> [ reader.name ]
  Done _ -> []
  Apply applied -> runExists (\(Applied function argument) -> names function <> names argument) applied

data Command = Hello | Bye

instance Show Command where
  show Hello = "hello"
  show Bye = "bye"

command :: Parser Command
command = Option (Reader { name: "command", read: readCommand })
  where
  readCommand "hello" = Right Hello
  readCommand "bye" = Right Bye
  readCommand "" = Left Empty
  readCommand word = Left (Unknown word)

modifier :: Parser (Command -> Command)
modifier = Option (Reader { name: "modifier", read: readModifier })
  where
  readModifier "" = Left Empty
  readModifier _ = Right identity

both :: Parser (Command -> Command)
both = (>>>) <$> modifier <*> modifier

main :: Effect Unit
main = do
  let parser = both <*> command
  log (show (names parser))
  log (show (parse parser "bye"))
  log (show (parse parser "hello"))
  log (show (parse parser "wave"))
  log (show (parse parser ""))
