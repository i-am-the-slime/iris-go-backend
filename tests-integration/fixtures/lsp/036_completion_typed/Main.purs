module Main where

data Maybe a = Just a | Nothing

fromMaybe :: forall a. a -> Maybe a -> a
fromMaybe _ (Just a) = a
fromMaybe a Nothing = a

life :: Int
life = 42

name :: String
name = "hello"

check = fromMaybe life
--                     ^
