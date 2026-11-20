module Header where

type Header = { name :: String, value :: String }

foreign import header :: Header
