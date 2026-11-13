module Main where

import Prelude

import Unsafe.Coerce (unsafeCoerce)

data Value

toValue :: forall a. a -> Value
toValue = unsafeCoerce

fromValue :: forall a. Value -> a
fromValue = unsafeCoerce

values :: Array Value
values = [ toValue 1, toValue 2 ]

main :: Array Int
main = map (\value -> fromValue value + 1) values <> [ fromValue (toValue "text" # fromValue # toValue) # identity # const 3 ]
