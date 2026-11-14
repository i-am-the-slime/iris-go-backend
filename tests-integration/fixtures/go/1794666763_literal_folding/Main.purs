module Main where

import Prelude

opaque :: forall a. Eq a => a -> a -> a
opaque sentinel x = if x == sentinel then opaque sentinel x else x

int :: Int -> Int
int = opaque 12345

number :: Number -> Number
number = opaque 12345.0

string :: String -> String
string = opaque "sentinel"

pair :: forall a. Show a => a -> a -> String
pair folded computed = show folded <> "/" <> show computed

inverse :: Number -> Number
inverse x = 1.0 / x

main :: Array String
main =
  [ pair (2147483647 + 1) (int 2147483647 + 1)
  , pair (-2147483648 - 1) (int (-2147483648) - 1)
  , pair (65536 * 65536) (int 65536 * 65536)
  , pair (2147483647 * 2147483647) (int 2147483647 * 2147483647)
  , pair (123456789 * 987654321) (int 123456789 * 987654321)
  , pair (negate (-2147483648)) (negate (int (-2147483648)))
  , pair (7 / 2) (int 7 / 2)
  , pair ((-7) / 2) (int (-7) / 2)
  , pair (7 / (-2)) (int 7 / (-2))
  , pair ((-7) / (-2)) (int (-7) / (-2))
  , pair (7 `mod` (-2)) (int 7 `mod` (-2))
  , pair ((-7) `mod` 2) (int (-7) `mod` 2)
  , pair ((-7) `mod` (-2)) (int (-7) `mod` (-2))
  , pair (5 / 0) (int 5 / 0)
  , pair (5 `mod` 0) (int 5 `mod` 0)
  , pair ((-2147483648) / (-1)) (int (-2147483648) / (-1))
  , pair (0.1 + 0.2) (number 0.1 + 0.2)
  , pair (inverse (0.0 * -1.0)) (inverse (number 0.0 * -1.0))
  , pair (inverse (-0.0)) (inverse (number (-0.0)))
  , pair (0.0 / 0.0) (number 0.0 / 0.0)
  , pair (1.0e308 * 10.0) (number 1.0e308 * 10.0)
  , pair (0.0 / 0.0 == 0.0 / 0.0) (number 0.0 / 0.0 == 0.0 / 0.0)
  , pair (0.0 / 0.0 < 1.0) (number 0.0 / 0.0 < 1.0)
  , pair (not (0.0 / 0.0 < 1.0)) (not (number 0.0 / 0.0 < 1.0))
  , pair (-0.0 == 0.0) (number (-0.0) == 0.0)
  , pair (1.0 / 3.0) (number 1.0 / 3.0)
  , pair ("a" <> "b") (string "a" <> "b")
  , pair ("é" < "z") (string "é" < "z")
  , pair ("😀" < "\xFFFF") (string "😀" < "\xFFFF")
  , pair ('a' < 'b') ('a' < 'b')
  , pair (not (3 < 4)) (not (int 3 < 4))
  , pair (if 1 < 2 then true else false) (if int 1 < 2 then true else false)
  , pair (if 1 < 2 then false else true) (if int 1 < 2 then false else true)
  , pair ((int 5 + 1) + 2) ((int 5 + 1) + 2)
  , pair ((2147483647 + int 1) + 1) ((int 2147483647 + 1) + 1)
  , pair ("x" <> ("y" <> string "z")) ("x" <> ("y" <> string "z"))
  , pair (0 >= 0 && int 3 < 4) (int 0 >= 0 && int 3 < 4)
  ]
