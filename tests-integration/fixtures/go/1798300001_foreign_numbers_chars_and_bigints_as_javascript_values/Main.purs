module Main where

import Prelude

import Control.Monad.Except (runExcept)
import Data.Array as Array
import Data.Either (Either)
import Data.Nullable (Nullable)
import Data.Nullable as Nullable
import Foreign (Foreign, readInt, readNumber, typeOf, unsafeToForeign)
import JS.BigInt (BigInt)
import JS.BigInt as BigInt
import Yoga.JSON (readJSON, writeJSON)

main :: Array String
main =
  [ typeOf (unsafeToForeign mixed)
  , show (runExcept (readNumber (unsafeToForeign 7)))
  , show (runExcept (readInt (unsafeToForeign (-200))))
  , writeJSON 'a'
  , writeJSON (BigInt.fromInt 10)
  , writeJSON { letter: 'x', big: BigInt.fromInt 7, missing: Nullable.null :: Nullable Int }
  , show (readJSON "\"a\"" :: Either _ Char)
  , show (readJSON "{\"big\":12}" :: Either _ { big :: BigInt })
  ]
  where
  mixed :: Array Foreign
  mixed = Array.snoc (Array.snoc [] (unsafeToForeign 1)) (unsafeToForeign "Freddy")
