module Main where

import Prelude

import Unsafe.Coerce (unsafeCoerce)

type Transform a = Show a => a -> String

after :: forall a. String -> Transform a
after prefix value = prefix <> show value

interleaved :: forall a b. Show a => a -> Eq b => b -> b -> String
interleaved value left right = if left == right then show value else "different"

boxed :: forall a. Show a => { describe :: a -> String }
boxed = { describe: \value -> "boxed " <> show value }

relabelled :: forall a. Show a => { describe :: a -> String }
relabelled = (unsafeCoerce :: (forall b. Show b => { describe :: b -> String }) -> (Show a => { describe :: a -> String })) boxed

describeSeven :: { describe :: Int -> String } -> String
describeSeven described = described.describe 7

local :: String
local = nested "local=" 13
  where
  nested :: forall a. String -> Transform a
  nested prefix value = prefix <> show value

main :: Array String
main =
  [ after "value=" 42
  , after "text=" "x"
  , interleaved true 1 1
  , interleaved 'c' "x" "y"
  , describeSeven relabelled
  , local
  ]
