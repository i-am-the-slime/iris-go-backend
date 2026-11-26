module Main where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Maybe (Maybe(..))
import Data.String as String

-- | A node of a name tree that keeps its children in an array, boxed since it is larger than a
-- | few words; finding a child gives a `Maybe` of the boxed node.
data TreeNode = TreeNode
  { name :: String
  , children :: Array TreeNode
  , label :: Maybe String
  , depth :: Int
  }

inserted :: TreeNode -> String -> TreeNode
inserted root path = insertAt (String.split (String.Pattern ".") path) root
  where
  insertAt parts (TreeNode node) = case Array.uncons parts of
    Nothing -> TreeNode node
    Just { head: part, tail: rest } -> do
      let existing = Array.find (\(TreeNode child) -> child.name == part) node.children
      let child = case existing of
            Just found -> found
            Nothing -> TreeNode { name: part, children: [], label: Nothing, depth: node.depth + 1 }
      let updated = if Array.null rest then labelled path child else insertAt rest child
      TreeNode (node { children = replaced part updated node.children })
  labelled label (TreeNode node) = TreeNode (node { label = Just label })
  replaced part child children
    | Array.any (\(TreeNode other) -> other.name == part) children =
        children <#> \other@(TreeNode node) -> if node.name == part then child else other
    | otherwise = Array.snoc children child

names :: TreeNode -> Array String
names (TreeNode node) = [ node.name ] <> Array.concatMap names node.children

main :: Array String
main = do
  let root = TreeNode { name: "root", children: [], label: Nothing, depth: 0 }
  names (foldl inserted root [ "a.b", "a.c", "d", "a.b.e" ])
