module Main where

import Prelude

import Data.Functor.Variant (VariantF, case_, inj, on)
import Type.Proxy (Proxy(..))

data Say a = Say String a

instance Functor Say where
  map f (Say text next) = Say text (f next)

data Count a = Count (Int -> a)

instance Functor Count where
  map f (Count next) = Count (f <<< next)

type Effects = (say :: Say, count :: Count)

describe :: VariantF Effects Int -> String
describe = case_
  # on (Proxy :: Proxy "count") (\(Count next) -> "count " <> show (next 2))
  # on (Proxy :: Proxy "say") (\(Say text next) -> text <> " " <> show next)

say :: VariantF Effects Int
say = inj (Proxy :: Proxy "say") (Say "hello" 4)

count :: VariantF Effects Int
count = inj (Proxy :: Proxy "count") (Count (_ + 1))

main :: Array String
main = [ describe say, describe count, describe (map (_ * 10) say), describe (map (_ * 10) count) ]
