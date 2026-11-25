module Main where

import Prelude

import Data.Either (Either(..), either)
import Effect (Effect)
import Journal (log)

class ParseError e where
  endOfInput :: e
  describe :: e -> String

newtype Problem = Problem String

instance ParseError Problem where
  endOfInput = Problem "end"
  describe (Problem text) = "problem: " <> text

newtype Code = Code Int

instance ParseError Code where
  endOfInput = Code 404
  describe (Code code) = "code " <> show code

newtype Parser e a = Parser (ParseError e => Int -> Either e a)

runParser :: forall e a. ParseError e => Parser e a -> Int -> Either e a
runParser (Parser parse) = parse

positive :: forall e. Parser e Int
positive = Parser \n -> if n > 0 then Right n else Left endOfInput

report :: forall e. ParseError e => Parser e Int -> Int -> String
report parser = runParser parser >>> either describe show

main :: Effect Unit
main = do
  log (report (positive :: Parser Problem Int) 0)
  log (report (positive :: Parser Problem Int) 3)
  log (report (positive :: Parser Code Int) (-1))
