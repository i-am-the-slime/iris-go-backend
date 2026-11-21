module Server where

import Prelude

import Effect (Effect)
import Effect.Uncurried (EffectFn2, EffectFn3)

type Routes =
  { handle :: EffectFn3 String String (String -> Effect Unit) Unit
  , add :: Int -> Int -> Int
  , each :: Array (String -> String -> Effect Unit)
  , settings :: Settings
  }

type Settings = { greeting :: String -> String -> String }

type Hooks =
  { route :: String -> EffectFn2 String (String -> Effect Unit) Unit
  , fold :: (Number -> Number -> Number) -> Number
  }

foreign import log :: String -> Effect Unit
foreign import serve :: Routes -> Effect Unit
foreign import installHooks :: Effect Hooks
