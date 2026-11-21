module Main where

import Prelude

import Data.Variant (Variant, inj)
import Foreign (unsafeToForeign)
import Foreign.Object as Object
import Type.Proxy (Proxy(..))
import Yoga.JSON (unsafeStringify, writeJSON)

type Shape = Variant
  ( name :: String
  , point :: { x :: Int }
  , count :: Int
  , ratio :: Number
  , flag :: Boolean
  , tags :: Array String
  )

shapes :: Array Shape
shapes =
  [ inj (Proxy :: _ "name") "a"
  , inj (Proxy :: _ "point") { x: 1 }
  , inj (Proxy :: _ "count") 3
  , inj (Proxy :: _ "ratio") 1.5
  , inj (Proxy :: _ "flag") true
  , inj (Proxy :: _ "tags") [ "p", "q" ]
  ]

main :: Array String
main = do
  let shared = unsafeToForeign (show 12)
  map writeJSON shapes <> [ unsafeStringify (Object.insert "e" shared (Object.singleton "f" shared)) ]
