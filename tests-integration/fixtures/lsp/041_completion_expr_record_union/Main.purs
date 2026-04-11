module Main where

class Union (l :: Row Type) (r :: Row Type) (u :: Row Type) | l r -> u, l u -> r, r u -> l

-- Test 1: direct Union constraint
type ButtonProps = (onClick :: String, disabled :: String, label :: String)

button
  :: forall given rest
   . Union given rest ButtonProps
  => Record given
  -> String
button _ = ""

testDirect :: String
testDirect = button {  }
--                   !^

-- Test 2: fixed record arg
fixed :: { name :: String, age :: String } -> String
fixed _ = ""

testFixed :: String
testFixed = fixed {  }
--                 !^

-- Test 3: FFIComponent-like type synonym with nested constraints
data JSX

class IsJSX (a :: Type)
instance IsJSX JSX
instance IsJSX String

class CoerceReactProps (given :: Type) (without :: Type) (target :: Type) | given -> without
instance (Union without missing target) => CoerceReactProps (Record without) x (Record target)

type FFIComponent props =
  forall givenProps nonDataProps kids
   . IsJSX kids
  => CoerceReactProps { | givenProps } { | nonDataProps } { | props }
  => { | givenProps }
  -> kids
  -> JSX

type DivProps = (className :: String, id :: String, title :: String)

div :: FFIComponent DivProps
div _ _ = unsafeCoerce unit
  where
  unsafeCoerce :: forall a b. a -> b
  unsafeCoerce _ = unsafeCoerce unit

testFFI :: JSX
testFFI = div {  } ""
--            !^
