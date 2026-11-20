module Timer where

foreign import data Timer :: Type

foreign import timer :: Number -> Timer
foreign import seconds :: Timer -> Number
