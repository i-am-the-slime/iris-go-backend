module Routes where

import Prelude

import Effect (Effect)
import Effect.Uncurried (EffectFn1, EffectFn2, EffectFn3)

foreign import data Reply :: Type

type Route =
  { path :: String
  , handle :: EffectFn3 String String Reply Unit
  , done :: EffectFn1 String Unit
  , prefixed :: String -> EffectFn2 String Reply Unit
  }

foreign import serve :: Route -> Effect Unit
foreign import call :: EffectFn3 String String Reply Unit -> Effect Unit
foreign import builtIn :: Route
foreign import noReply :: Reply
