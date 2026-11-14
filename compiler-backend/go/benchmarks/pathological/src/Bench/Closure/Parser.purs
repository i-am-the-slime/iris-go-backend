module Bench.Closure.Parser where

import Prelude

import Bench.Harness (benchmark)
import Control.Alt ((<|>))
import Control.Lazy (fix)
import Data.Array ((..))
import Data.Either (either)
import Data.Foldable (sum)
import Data.List (List)
import Data.String (joinWith)
import Effect (Effect)
import Parsing (Parser, runParser)
import Parsing.Combinators (between, sepBy)
import Parsing.String (char, string)
import Parsing.String.Basic (intDecimal, skipSpaces)

hypothesis :: String
hypothesis = "purescript-parsing is CPS: every combinator allocates success and failure continuations per character"

data Value
  = Number Int
  | Text String
  | Items (List Value)

main :: Effect Unit
main = benchmark { size: 3000, workload }

workload :: Int -> String
workload n = either show (show <<< total) (runParser (document n) value)
  where
  total = case _ of
    Number number -> number
    Text _ -> 1
    Items items -> sum (map total items)

document :: Int -> String
document n = "[" <> joinWith ", " (map entry (1 .. n)) <> "]"
  where
  entry i = "[" <> show i <> ", \"word\", [" <> show (i `mod` 7) <> ", " <> show (i `mod` 11) <> "], []]"

value :: Parser String Value
value = fix \self -> skipSpaces *> (number <|> text <|> items self) <* skipSpaces
  where
  number = Number <$> intDecimal
  text = Text <$> between (char '"') (char '"') (string "word")
  items self = Items <$> between (char '[') (char ']') (self `sepBy` char ',')
