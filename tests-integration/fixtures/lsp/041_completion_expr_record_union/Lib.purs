module Lib where

class Union (l :: Row Type) (r :: Row Type) (u :: Row Type) | l r -> u, l u -> r, r u -> l

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

type BaseHTMLAttributesF (r :: Row Type) = (className :: String, id :: String, title :: String | r)

type DivProps = BaseHTMLAttributesF ()

div :: FFIComponent DivProps
div _ _ = unsafeCoerce unit
  where
  unsafeCoerce :: forall a b. a -> b
  unsafeCoerce _ = unsafeCoerce unit
