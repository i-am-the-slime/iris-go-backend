module RedBlack where

import Prelude

data Color = Red | Black

data Tree = Leaf | Node Color Tree Int Boolean Tree

insert :: Int -> Boolean -> Tree -> Tree
insert k v tree
  | isRed tree = setBlack (ins k v tree)
  | otherwise = ins k v tree

ins :: Int -> Boolean -> Tree -> Tree
ins kx vx = case _ of
  Leaf -> Node Red Leaf kx vx Leaf
  Node Red a ky vy b -> case compare kx ky of
    LT -> Node Red (ins kx vx a) ky vy b
    GT -> Node Red a ky vy (ins kx vx b)
    EQ -> Node Red a kx vx b
  Node Black a ky vy b -> case compare kx ky of
    LT
      | isRed a -> balanceLeft (ins kx vx a) ky vy b
      | otherwise -> Node Black (ins kx vx a) ky vy b
    GT
      | isRed b -> balanceRight a ky vy (ins kx vx b)
      | otherwise -> Node Black a ky vy (ins kx vx b)
    EQ -> Node Black a kx vx b

balanceLeft :: Tree -> Int -> Boolean -> Tree -> Tree
balanceLeft left kv vv right = case left of
  Node _ (Node Red l kx vx r1) ky vy r2 -> Node Red (Node Black l kx vx r1) ky vy (Node Black r2 kv vv right)
  Node _ l1 ky vy (Node Red l2 kx vx r) -> Node Red (Node Black l1 ky vy l2) kx vx (Node Black r kv vv right)
  Node _ l ky vy r -> Node Black (Node Red l ky vy r) kv vv right
  Leaf -> Leaf

balanceRight :: Tree -> Int -> Boolean -> Tree -> Tree
balanceRight left kv vv right = case right of
  Node _ (Node Red l kx1 vx1 r1) ky vy r2 -> Node Red (Node Black left kv vv l) kx1 vx1 (Node Black r1 ky vy r2)
  Node _ l1 ky vy (Node Red l2 kx2 vx2 r2) -> Node Red (Node Black left kv vv l1) ky vy (Node Black l2 kx2 vx2 r2)
  Node _ l ky vy r -> Node Black left kv vv (Node Red l ky vy r)
  Leaf -> Leaf

isRed :: Tree -> Boolean
isRed = case _ of
  Node Red _ _ _ _ -> true
  _ -> false

setBlack :: Tree -> Tree
setBlack = case _ of
  Node _ l k v r -> Node Black l k v r
  Leaf -> Leaf

size :: Tree -> Int
size = case _ of
  Leaf -> 0
  Node _ l _ _ r -> size l + 1 + size r

checksum :: Tree -> Int
checksum = go 0
  where
  go acc = case _ of
    Leaf -> acc
    Node _ l k v r -> go (go acc l + (if v then k else 1)) r

valid :: Tree -> Boolean
valid tree = blackHeight tree > 0 && ordered (-1000000) 1000000 tree

blackHeight :: Tree -> Int
blackHeight = case _ of
  Leaf -> 1
  Node color l _ _ r -> do
    let left = blackHeight l
    let right = blackHeight r
    if left < 0 || left /= right || redBelowRed color l r then -1
    else left + blackness color
  where
  redBelowRed color l r = case color of
    Red -> isRed l || isRed r
    Black -> false
  blackness = case _ of
    Red -> 0
    Black -> 1

ordered :: Int -> Int -> Tree -> Boolean
ordered low high = case _ of
  Leaf -> true
  Node _ l k _ r -> low < k && k < high && ordered low k l && ordered k high r
