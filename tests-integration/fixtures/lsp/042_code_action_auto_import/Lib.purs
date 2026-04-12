module Lib where

data Maybe a = Just a | Nothing

identity x = x

class MyClass a where
  myMethod :: a -> a
