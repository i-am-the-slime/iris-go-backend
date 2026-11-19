module Main where

import Prelude

import Data.Reflectable (class Reflectable, reflectType, reifyType)
import Type.Proxy (Proxy)

-- | `reifyType` hands its continuation a `Reflectable` dictionary that reflects the run-time
-- value, for every type that can be reified, also through functions that take the constraint.
doubled :: forall v. Reflectable v Int => Proxy v -> Int
doubled proxy = reflectType proxy * 2

shouted :: forall v. Reflectable v String => Proxy v -> String
shouted proxy = reflectType proxy <> "!"

flipped :: forall v. Reflectable v Boolean => Proxy v -> Boolean
flipped proxy = not (reflectType proxy)

described :: forall v. Reflectable v Ordering => Proxy v -> String
described proxy = case reflectType proxy of
  LT -> "less"
  EQ -> "equal"
  GT -> "greater"

labelled :: forall v. Reflectable v String => Proxy v -> Int -> String
labelled proxy n = reflectType proxy <> show n

labels :: String -> Array String
labels prefix = reifyType prefix \proxy -> map (labelled proxy) [ 1, 2, 3 ]

tagged :: forall v. Reflectable v Int => Proxy v -> Int -> String
tagged proxy k = "n=" <> show (reflectType proxy * 10 + k)

reifiedEach :: Int -> Array String -> Array String
reifiedEach n done
  | n > 3 = done
  | otherwise = reifiedEach (n + 1) (done <> [ reifyType n tags ])
      where
      tags :: forall v. Reflectable v Int => Proxy v -> String
      tags proxy = tagged proxy n <> tagged proxy 1

reifiedInt :: Int -> Int
reifiedInt n = reifyType n doubled

main :: Array String
main =
  [ show (reifiedInt 21)
  , show (reifiedInt (-4))
  , show (reifyType 7 reflectType)
  , reifyType "erin" shouted
  , show (reifyType true flipped)
  , show (reifyType false reflectType)
  , reifyType GT described
  , show (labels "item")
  , show (reifiedEach 0 [])
  , show (map (\ordering -> reifyType ordering reflectType) [ LT, EQ, GT ])
  ]
