module Main where

import Prim.Row (class Union)

data JSX

class IsJSX :: Type -> Constraint
class IsJSX a

instance IsJSX JSX
instance IsJSX String
instance IsJSX (Array JSX)

class CoerceProps :: Type -> Type -> Constraint
class CoerceProps props targetProps | props -> targetProps

instance Union props missing targetProps
  => CoerceProps { | props } { | targetProps }

type BaseAttrs = (className :: String)

type Component props = forall given target kids
   . IsJSX kids
  => CoerceProps { | given } { | props }
  => { | given }
  -> kids
  -> JSX

foreign import div :: Component BaseAttrs

test1 :: JSX
test1 = div { className: "hello" } ([] :: Array JSX)

test2 = div { className: "hello" } ([] :: Array JSX)
