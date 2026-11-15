module Main where

import Prelude

import Data.Lens (Iso', Lens', Prism', Traversal', iso, lens, over, preview, prism', review, traverseOf, traversed, view)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Type.Proxy (Proxy(..))

type Point = { x :: Int, tags :: Array String }

data Shape = Circle Int | Square Int

_x :: forall r. Lens' { x :: Int | r } Int
_x = prop (Proxy @"x")

_tags :: Traversal' Point String
_tags = prop (Proxy @"tags") <<< traversed

_circle :: Prism' Shape Int
_circle = prism' Circle case _ of
  Circle radius -> Just radius
  Square _ -> Nothing

_doubled :: Iso' Int Int
_doubled = iso (_ * 2) (_ / 2)

_first :: Lens' { first :: Int, second :: Int } Int
_first = lens _.first (_ { first = _ })

bump :: Int -> Point -> Point
bump 0 point = point
bump n point = bump (n - 1) (over _x (_ + view _doubled n) point)

origin :: Point
origin = { x: 3, tags: [ "a", "b" ] }

main :: Array String
main =
  [ show (view (_x <<< _doubled) origin)
  , show (over _x (_ + 1) origin).x
  , show (preview _circle (Circle 2))
  , show (preview _circle (Square 2))
  , case review _circle 5 of
      Circle radius -> show radius
      Square side -> show side
  , show (traverseOf _tags (\tag -> if tag == "" then Nothing else Just (tag <> "!")) origin <#> _.tags)
  , show (view _first { first: 1, second: 2 })
  , show (view _x (bump 3 origin))
  ]
