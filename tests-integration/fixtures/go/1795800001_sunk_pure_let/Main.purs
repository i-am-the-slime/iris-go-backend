module Main where

import Prelude

import Data.Either (Either(..), isLeft)
import Data.Int as Int
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Exception (throw)

data Problem = NotACount (Array String) Number

-- | `problem` is built inside the two branches that fail, `value < 0.0` and a fraction, so a
-- | whole count builds no `NotACount`.
readCount :: String -> Number -> Either Problem Int
readCount label value = do
  let problem = Left (NotACount [ label, "count" ] value)
  if value < 0.0 then problem
  else case Int.fromNumber value of
    Nothing -> problem
    Just count -> Right count

-- | `shared` is used on every path, so it stays where it is, built once.
describe :: String -> Int -> Array String
describe label count = do
  let shared = [ label, show count ]
  if count > 10 then shared <> shared else shared

main :: Effect Unit
main = do
  let counts = map (readCount "apples") [ 3.0, 2.5, -1.0 ]
  when (map isLeft counts /= [ false, true, true ]) do
    throw "a count is read wrongly"
  when (map (describe "pears") [ 11, 1 ] /= [ [ "pears", "11", "pears", "11" ], [ "pears", "1" ] ]) do
    throw "the shared value is wrong"
