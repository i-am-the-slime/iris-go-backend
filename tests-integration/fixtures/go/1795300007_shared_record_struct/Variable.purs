module Variable where

type Variable = { name :: String, value :: String }

foreign import variable :: Variable
