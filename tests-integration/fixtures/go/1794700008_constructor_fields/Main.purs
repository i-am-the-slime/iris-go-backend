module Main where

import Prelude

import Data.Either (Either(..))
import Data.Foldable (foldl)
import Data.List (List(..), (:))
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))

-- A constructor's one field is named after it: `Just`, `Left`, `Right`.
-- The fields of a type's one constructor are named by ordinal: `First`, `Second`.
-- `Cons` has two fields among two constructors and keeps `Cons0`, `Cons1`.
total :: Array (Tuple (Maybe Int) (Either String Int)) -> List Int -> Int
total pairs list = foldl step 0 pairs + sum list
  where
  step acc (Tuple (Just value) (Right more)) = acc + value + more
  step acc (Tuple _ (Left _)) = acc - 1
  step acc _ = acc
  sum Nil = 0
  sum (head : tail) = head + sum tail

-- A constructor named `Tag` would take the tag's name: the type keeps
-- positional names.
data Labelled = Tag String | Untagged

label :: Labelled -> String
label (Tag name) = name
label Untagged = "none"

-- A constructor named like the slots that others share keeps its own slots.
data Entry = Field Int Int | Duo String String | Trio String String

entry :: Entry -> String
entry (Field left right) = show (left - right)
entry (Duo left right) = left <> right
entry (Trio left right) = right <> left

main :: String
main = show (total [ Tuple (Just 1) (Right 2), Tuple Nothing (Left "x") ] (3 : 4 : Nil))
  <> show (map label [ Tag "t", Untagged ])
  <> show (map entry [ Field 5 1, Duo "a" "b", Trio "c" "d" ])
