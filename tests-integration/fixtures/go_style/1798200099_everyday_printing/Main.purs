module Fun.Printing where

import Prelude

import Data.Int (toNumber, round, floor, ceil, fromNumber, toStringAs, hexadecimal, binary, radix, fromStringAs, pow, quot, rem)
import Data.Number (nan, infinity, sqrt)
import Data.Maybe (fromMaybe)
import Data.String.CodeUnits (toCharArray, fromCharArray, singleton)
import Data.String (length, toUpper, toLower)
import Data.String.CodePoints as CodePoints
import Data.Char (toCharCode, fromCharCode)
import Effect (Effect)
import Effect.Console (log)
import Data.Foldable (for_)
import Data.Tuple.Nested ((/\))

main :: Effect Unit
main = do
  log "-- numbers"
  for_ numbers \n -> log (show n)
  log "-- number arithmetic"
  log $ show (0.1 + 0.2)
  log $ show (1.0 / 3.0)
  log $ show (2.0 / 3.0)
  log $ show (100.0 / 7.0)
  log $ show (1.0e21 + 1.0)
  log $ show (123456789.0 * 1000000000000.0)
  log $ show (1.0 / 0.0)
  log $ show (-1.0 / 0.0)
  log $ show (0.0 / 0.0)
  log $ show (-0.0)
  log $ show (0.0 * -1.0)
  log $ show (sqrt 2.0)
  log $ show (toNumber 7)
  log $ show (toNumber (-7))
  log $ show (5.0e-324)
  log $ show (1.7976931348623157e308)
  log $ show (1.0e-7)
  log $ show (1.0e-6)
  log $ show (123.456e10)
  log $ show (nan == nan)
  log $ show (compare 1.0 nan)
  log $ show (max 1.0 nan)
  log "-- rounding"
  for_ [ 2.5, -2.5, 0.5, -0.5, 1.5, 3.7, -3.7, 1.0e10, -1.0e10, 1.0e20, nan, infinity ] \n ->
    log (show n <> " round=" <> show (round n) <> " floor=" <> show (floor n) <> " ceil=" <> show (ceil n) <> " from=" <> show (fromNumber n))
  log "-- ints"
  log $ show (top :: Int)
  log $ show (bottom :: Int)
  log $ show ((top :: Int) + 1)
  log $ show ((bottom :: Int) - 1)
  log $ show ((top :: Int) * 2)
  log $ show (46341 * 46341)
  log $ show (negate (bottom :: Int))
  for_ [ 7 /\ 2, (-7) /\ 2, 7 /\ (-2), (-7) /\ (-2) ] \(a /\ b) ->
    log (show a <> " " <> show b <> " div=" <> show (a `div` b) <> " mod=" <> show (a `mod` b) <> " quot=" <> show (a `quot` b) <> " rem=" <> show (a `rem` b))
  log $ show (pow 2 31)
  log $ show (pow 2 10)
  log $ show (pow 3 (-1))
  log $ toStringAs hexadecimal 255
  log $ toStringAs hexadecimal (-255)
  log $ toStringAs binary 10
  log $ toStringAs (fromMaybe hexadecimal (radix 36)) 123456
  log $ show (fromStringAs hexadecimal "ff")
  log $ show (fromStringAs hexadecimal "-FF")
  log "-- strings"
  for_ strings \s -> log (show s <> " len=" <> show (length s) <> " cps=" <> show (CodePoints.length s))
  log $ show (toCharArray "héllo")
  log $ show (fromCharArray [ 'a', 'b', '\n' ])
  log $ show [ 'a', '\'', '"', '\\', '\t', '\x00', '\x7f', 'é', '\xffff' ]
  log $ show (toCharCode 'A')
  log $ show (fromCharCode 0x1F600)
  log $ show (fromCharCode 233)
  log $ show (singleton 'z')
  log $ toUpper "straße ﬁ"
  log $ toLower "İSTANBUL"
  log $ show (CodePoints.toCodePointArray "a😀b")
  log $ show (CodePoints.take 2 "😀😀😀")
  log $ show ("abc" < "abd") <> show ("Z" < "a") <> show ("é" > "z")
  log $ show (compare "a😀" "a\xffff")
  where
  numbers =
    [ 1.0, 0.0, -0.0, 1.5, -1.5, 100.0, 1.0e21, 1.0e20, 1.0e-7, 123456789012345680000.0, 1.0e100
    , 0.1, 3.14159, 2.0e-5, 1.23e-10, 9007199254740993.0, 4.35, 1.0e300 * 1.0e10, nan, infinity, -infinity
    ]
  strings =
    [ "", "plain", "quote\"s", "back\\slash", "tab\there", "new\nline", "cr\rx", "nul\x00x", "del\x7f"
    , "é", "日本語", "😀", "mixed 😀 é \t", "\x1b[0m", "\xd83d", "a\xffffb", "\x01\x1f", "line\x2028sep"
    ]
