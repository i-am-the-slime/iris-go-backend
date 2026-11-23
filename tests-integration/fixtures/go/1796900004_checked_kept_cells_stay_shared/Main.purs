module Main where

import Prelude

import Data.List (List(..), (:))
import Effect.Ref as Ref
import Effect.Unsafe (unsafePerformEffect)
import Keeper (keep, kept)
import RedBlack (Tree(..), checksum, insert)

stashed :: Ref.Ref Tree
stashed = unsafePerformEffect (Ref.new Leaf)

stash :: Tree -> Int
stash tree = unsafePerformEffect do
  Ref.write tree stashed
  pure (checksum tree)

storedInARef :: Int -> Int
storedInARef steps = go Leaf Nil 0 steps
  where
  go tree trail total n
    | n <= 0 = total + checksum tree
    | otherwise = do
        let next = insert n true tree
        go next (if n `mod` 4 == 0 then next : trail else trail) (if n == 7 then total + stash next else total) (n - 1)

returnedInARecord :: Int -> { kept :: Tree, total :: Int }
returnedInARecord steps = go Leaf Nil { kept: Leaf, total: 0 } steps
  where
  go tree trail record n
    | n <= 0 = record { total = record.total + checksum tree }
    | otherwise = do
        let next = insert n true tree
        go next (if n `mod` 4 == 0 then next : trail else trail) (if n == 7 then record { kept = next } else record) (n - 1)

capturedInAClosure :: Int -> { later :: Unit -> Int, total :: Int }
capturedInAClosure steps = go Leaf Nil (\_ -> 0) steps
  where
  go tree trail later n
    | n <= 0 = { later, total: checksum tree }
    | otherwise = do
        let next = insert n true tree
        go next (if n `mod` 4 == 0 then next : trail else trail) (if n == 7 then (\_ -> checksum next) else later) (n - 1)

passedToAForeign :: Int -> Int
passedToAForeign steps = go Leaf Nil 0 steps
  where
  go tree trail total n
    | n <= 0 = total + checksum tree
    | otherwise = do
        let next = insert n true tree
        go next (if n `mod` 4 == 0 then next : trail else trail) (if n == 7 then total + keep next else total) (n - 1)

main :: Array Int
main = unsafePerformEffect do
  let fromStoring = storedInARef 40
  fromTheRef <- if fromStoring > 0 then Ref.read stashed else pure Leaf
  let record = returnedInARecord 40
  let closure = capturedInAClosure 40
  let fromKeeping = passedToAForeign 40
  fromTheForeign <- if fromKeeping > 0 then kept else pure Leaf
  pure
    [ fromStoring
    , checksum fromTheRef
    , record.total
    , checksum record.kept
    , closure.total
    , closure.later unit
    , fromKeeping
    , checksum fromTheForeign
    ]
