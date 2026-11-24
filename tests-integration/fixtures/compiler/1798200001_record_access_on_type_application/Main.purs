module Main where

class Describe a where
  describe :: a -> String

instance Describe Int where
  describe _ = "Int"

described :: forall @a. Describe a => a -> { label :: String }
described value = { label: describe value }

defaulted :: forall @a. Describe a => { name :: String }
defaulted = { name: "defaulted" }

accessAfterApplication = (described @Int 1).label

accessAfterTypeApplication = (defaulted @Int).name

accessNested = { outer: defaulted @Int }.outer.name
