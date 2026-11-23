module Main where

import Prelude

import Effect.Ref as Ref
import Effect.Unsafe (unsafePerformEffect)
import Keeper (keep, kept)

data Tree = Leaf | Node Tree Int Tree

sample :: Int -> Tree
sample depth
  | depth == 0 = Leaf
  | otherwise = Node (sample (depth - 1)) depth (sample (depth - 1))

total :: Tree -> Int
total = case _ of
  Leaf -> 0
  Node left value right -> total left + value + total right

incremented :: Tree -> Tree
incremented = case _ of
  Leaf -> Leaf
  Node left value right -> Node (incremented left) (value + 1) (incremented right)

stashed :: Ref.Ref Tree
stashed = unsafePerformEffect (Ref.new Leaf)

stashedAfter :: Int -> Tree -> Int
stashedAfter countdown tree
  | countdown == 0 = unsafePerformEffect do
      Ref.write tree stashed
      pure (total tree)
  | otherwise = stashedAfter (countdown - 1) tree

storedInARef :: Int -> Int
storedInARef depth = do
  let tree = sample depth
  if stashedAfter 2 tree > 0 then total (incremented tree) else 0

withTotalAfter :: Int -> Tree -> { total :: Int, tree :: Tree }
withTotalAfter countdown tree
  | countdown == 0 = { total: total tree, tree }
  | otherwise = withTotalAfter (countdown - 1) tree

returnedInARecord :: Int -> Int
returnedInARecord depth = do
  let tree = sample depth
  let record = withTotalAfter 2 tree
  if record.total > 0 then total (incremented tree) * 1000 + total record.tree else 0

totalLaterAfter :: Int -> Tree -> Unit -> Int
totalLaterAfter countdown tree
  | countdown == 0 = \_ -> total tree
  | otherwise = totalLaterAfter (countdown - 1) tree

capturedInAClosure :: Int -> Int
capturedInAClosure depth = do
  let tree = sample depth
  let later = totalLaterAfter 2 tree
  if later unit > 0 then total (incremented tree) * 1000 + later unit else 0

keptAfter :: Int -> Tree -> Int
keptAfter countdown tree
  | countdown == 0 = keep tree
  | otherwise = keptAfter (countdown - 1) tree

passedToAForeign :: Int -> Int
passedToAForeign depth = do
  let tree = sample depth
  if keptAfter 2 tree > 0 then total (incremented tree) else 0

main :: Array Int
main = unsafePerformEffect do
  let fromStoring = storedInARef 3
  fromTheRef <- if fromStoring > 0 then Ref.read stashed else pure Leaf
  let fromKeeping = passedToAForeign 3
  fromTheForeign <- if fromKeeping > 0 then kept else pure Leaf
  pure
    [ fromStoring
    , total fromTheRef
    , returnedInARecord 3
    , capturedInAClosure 3
    , fromKeeping
    , total fromTheForeign
    ]
