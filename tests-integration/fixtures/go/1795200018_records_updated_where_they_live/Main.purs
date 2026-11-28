module Main where

import Prelude

import Data.Foldable (foldl)
import Data.FoldableWithIndex (foldlWithIndex)
import Data.Tuple (Tuple(..))

type Body = { x :: Number, y :: Number, vx :: Number, vy :: Number, mass :: Number }

pull :: Body -> Body -> Body
pull other acc = do
  let dx = other.x - acc.x
  let dy = other.y - acc.y
  acc { vx = acc.vx + dx * other.mass, vy = acc.vy + dy * other.mass }

attract :: Array Body -> Body -> Body
attract others body = foldl (\acc other -> pull other acc) body others

attractOthers :: Int -> Array Body -> Body -> Body
attractOthers i others body = foldlWithIndex (\j acc other -> if i == j then acc else pull other acc) body others

weighedSum :: Array Body -> Number
weighedSum bodies = foldlWithIndex (\i total body -> total + toNumber i * body.mass) 0.0 bodies

pairs :: Array Int -> Array (Tuple Int Int)
pairs numbers = foldlWithIndex (\i acc n -> acc <> [ Tuple i n ]) [] numbers

toNumber :: Int -> Number
toNumber i = if i == 0 then 0.0 else 1.0 + toNumber (i - 1)

main :: Number
main = do
  let bodies = [ { x: 0.0, y: 0.0, vx: 0.0, vy: 0.0, mass: 1.0 }, { x: 1.0, y: 2.0, vx: 0.0, vy: 0.0, mass: 0.5 } ]
  let moved = attract bodies { x: 0.5, y: 0.5, vx: 0.0, vy: 0.0, mass: 2.0 }
  let pulled = attractOthers 1 bodies { x: 0.5, y: 0.5, vx: 0.0, vy: 0.0, mass: 2.0 }
  moved.vx + moved.vy + pulled.vx + weighedSum bodies + toNumber (foldl (\s (Tuple i n) -> s + i * n) 0 (pairs [ 3, 4 ]))
