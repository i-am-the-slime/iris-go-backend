module Main where

class Describe a where
  describe :: a -> String

instance Describe Int where
  describe _ = "int"

instance Describe a => Describe (Array a) where
  describe _ = "array"

newtype Tree = Tree (Array Tree)

derive newtype instance Describe Tree

newtype Leaves = Leaves (Array Int)

derive newtype instance Describe Leaves

newtype Wrapped a = Wrapped (Array a)

derive newtype instance Describe a => Describe (Wrapped a)
