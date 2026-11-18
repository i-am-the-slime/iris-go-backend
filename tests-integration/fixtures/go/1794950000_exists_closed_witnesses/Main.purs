module Main where

import Prelude

import Data.Exists (Exists, mkExists, runExists)

data Described a = Described a (a -> String) (a -> a)

type Anything = Exists Described

described :: forall a. a -> (a -> String) -> (a -> a) -> Anything
described value describe next = mkExists (Described value describe next)

step :: Anything -> Anything
step = runExists \(Described value describe next) -> mkExists (Described (next value) describe next)

render :: Anything -> String
render = runExists \(Described value describe _) -> describe value

describeTwice :: forall a. Described a -> String
describeTwice (Described value describe next) = describe value <> describe (next value)

renderTwice :: Anything -> String
renderTwice = runExists describeTwice

main :: Array String
main = map (\thing -> render (step thing) <> renderTwice thing) things

things :: Array Anything
things =
  [ described 1 show (_ + 1)
  , described "a" identity (_ <> "!")
  , described [ 1.5 ] show (map (_ * 2.0))
  ]
