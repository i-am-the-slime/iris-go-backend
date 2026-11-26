module Main where

import Prelude

import Data.Array ((..))
import Data.Array as Array
import Data.Foldable (foldl)
import Data.Maybe (fromMaybe)

type Board = { cells :: Array Int, moves :: Int }

marked :: Board -> Int -> Board
marked board position =
  { cells: fromMaybe board.cells (Array.updateAt position (position + 10) board.cells)
  , moves: board.moves + 1
  }

played :: Array Int -> Board
played cells = foldl marked { cells, moves: 0 } (1 .. 3)

main :: Array String
main = do
  let shared = Array.replicate 5 0
  let board = played shared
  [ show board.cells
  , show board.moves
  , show shared
  ]
