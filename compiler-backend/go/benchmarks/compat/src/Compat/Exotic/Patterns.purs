module Compat.Exotic.Patterns where

import Prelude

import Data.Array as Array
import Data.List (List(..), (:))
import Data.Maybe (Maybe(..))
import Data.String.CodeUnits as String
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Effect.Console (log)

type Config = { "type" :: String, "content-length" :: Int, nested :: { inner :: { value :: Int } } }

classify :: Array Int -> String
classify [] = "empty"
classify [ x ] = "one " <> show x
classify [ 0, y ] = "zero then " <> show y
classify [ x, y ] | x == y = "pair of " <> show x
                  | x > y = "descending"
classify xs@[ _, _, _ ] = "three " <> show (Array.length xs)
classify _ = "many"

walk :: List Int -> String
walk (a : b : rest) | a < b = "up " <> walk (b : rest)
walk (a : rest@(b : _)) | a > b = "down " <> walk rest
walk (_ : rest) = "flat " <> walk rest
walk Nil = "end"

describe :: Config -> String
describe { "type": kind, "content-length": length, nested: { inner: { value } } } = kind <> "/" <> show length <> "/" <> show value

letters :: Char -> String
letters 'a' = "vowel a"
letters c | c >= 'b' && c <= 'z' = "consonant-ish " <> String.singleton c
          | otherwise = "other"

nestedMaybe :: Maybe (Maybe (Array (Int /\ String))) -> String
nestedMaybe (Just (Just [ n /\ s ])) = s <> show n
nestedMaybe (Just (Just _)) = "some"
nestedMaybe (Just Nothing) = "inner nothing"
nestedMaybe Nothing = "nothing"

collatzLength :: Int -> Int
collatzLength = go 0
  where
  go acc 1 = acc
  go acc n
    | even n = go (acc + 1) (n / 2)
    | otherwise = go (acc + 1) (3 * n + 1)
  even n = n `mod` 2 == 0

main :: Effect Unit
main = do
  log (show (map classify [ [], [ 1 ], [ 0, 5 ], [ 2, 2 ], [ 3, 1 ], [ 1, 3 ], [ 1, 2, 3 ], [ 1, 2, 3, 4 ] ]))
  log (walk (1 : 2 : 2 : 1 : 5 : Nil))
  log (describe { "type": "json", "content-length": 42, nested: { inner: { value: 7 } } })
  log (show (map letters [ 'a', 'q', '!' ]))
  log (show (map nestedMaybe [ Just (Just [ 1 /\ "x" ]), Just (Just []), Just Nothing, Nothing ]))
  log (show (collatzLength 97))
  let { "type": t } = { "type": "record", other: 1 }
  log t
  let isOdd n = if n == 0 then false else isEven' (n - 1)
      isEven' n = if n == 0 then true else isOdd (n - 1)
  log (show (isOdd 9))
