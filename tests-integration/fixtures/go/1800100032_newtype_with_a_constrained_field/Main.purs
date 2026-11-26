module Main where

import Prelude
import Data.Either (Either(..))

class ParseError e where
  endOfInput :: e

newtype Problem = Problem String

instance Show Problem where
  show (Problem s) = "Problem " <> s

instance ParseError Problem where
  endOfInput = Problem "end"

newtype Parser e a = Parser (ParseError e => Int -> Either e a)

runParser :: forall e a. ParseError e => Parser e a -> Int -> Either e a
runParser (Parser f) = f

positive :: forall e. Parser e Int
positive = Parser \n -> if n > 0 then Right n else Left endOfInput

main :: Array String
main =
  [ show (runParser (positive :: Parser Problem Int) 0)
  , show (runParser (positive :: Parser Problem Int) 5)
  ]
