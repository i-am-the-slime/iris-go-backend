module Main where

data Maybe a = Just a | Nothing

fromMaybe :: forall a. a -> Maybe a -> a
fromMaybe _ (Just a) = a
fromMaybe a Nothing = a

ex :: String
ex = do
  let fallback = "fb"
  fromMaybe fallback (Just "Hello")
--            ^
