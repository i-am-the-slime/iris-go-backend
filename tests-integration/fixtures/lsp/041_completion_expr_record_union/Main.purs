module Main where

class Union (l :: Row Type) (r :: Row Type) (u :: Row Type) | l r -> u, l u -> r, r u -> l

type ButtonProps = (onClick :: String, disabled :: String, label :: String)

button
  :: forall given rest
   . Union given rest ButtonProps
  => Record given
  -> String
button _ = ""

testExprRecord :: String
testExprRecord = button {  }
--                       !^

fixed :: { name :: String, age :: String } -> String
fixed _ = ""

testFixedRecord :: String
testFixedRecord = fixed {  }
--                       !^
