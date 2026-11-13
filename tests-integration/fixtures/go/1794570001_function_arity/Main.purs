module Main where

import Prelude

import Data.Array (foldl)

type Church a = (a -> a) -> a -> a

zeroC :: forall a. Church a
zeroC _ x = x

succC :: forall a. Church a -> Church a
succC n f x = f (n f x)

mulC :: forall a. Church a -> Church a -> Church a
mulC m n f x = m (n f) x

fromInt :: Int -> Church Int
fromInt 0 = zeroC
fromInt n = succC (fromInt (n - 1))

toInt :: Church Int -> Int
toInt n = n (_ + 1) 0

repeat :: Int -> String
repeat 0 = ""
repeat n = "*" <> repeat (n - 1)

prepared :: Int -> String -> String
prepared = \a -> let prefix = repeat a in \b -> prefix <> b

shared :: (Int -> Int -> Int) -> Int -> Array Int
shared op seed =
  let
    partial = op (seed * seed)
  in
    [ op 1 2, partial 3, partial 4 ]

curried :: (Int -> String -> String) -> Array String
curried f =
  let
    g = f 4
  in
    [ f 1 "a", g "b", g "c" ]

type Operations = { combine :: Int -> Int -> Int }

reduce :: Operations -> Array Int -> Int
reduce operations = foldl operations.combine 0

main :: Array String
main =
  [ show (toInt (mulC (fromInt 3) (fromInt 4))) ]
    <> map (show <<< shared (\a b -> a * 10 + b)) [ 1, 2 ]
    <> map (show <<< curried) [ prepared, \a b -> show a <> b ]
    <> map (\combine -> show (reduce { combine } [ 1, 2, 3 ])) [ add, \a b -> a * b + 1 ]
