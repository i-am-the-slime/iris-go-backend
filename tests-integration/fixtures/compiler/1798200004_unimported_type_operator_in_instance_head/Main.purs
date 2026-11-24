module Main where

data Tuple a b = Tuple a b

class Describe a where
  describe :: a -> String

instance Describe a => Describe (a /\ b) where
  describe _ = "pair"
