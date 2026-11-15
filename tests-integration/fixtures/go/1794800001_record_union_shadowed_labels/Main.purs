module Main where

import Prelude

import Record as Record
import Record.Builder as Builder

type Defaults = { a :: String, z :: Char }

defaults :: Defaults
defaults = { a: "shadowed", z: 'z' }

overridden :: { a :: Int } -> String
overridden override = show union.a <> " " <> show union.z
  where
  union = Record.union override defaults

built :: { a :: Int, z :: Char }
built = Builder.build (Builder.nub <<< Builder.union { a: 2 }) defaults

merged :: { a :: Int, z :: Char }
merged = Builder.build (Builder.merge { a: 3 }) defaults

flipped :: { a :: String, z :: Char }
flipped = Builder.build (Builder.flip Builder.merge { a: 4 }) defaults

main :: Array String
main =
  [ overridden { a: 1 }
  , show built
  , show merged
  , show flipped
  , show (Record.nub (Record.union { z: 'y' } defaults))
  , show (Record.disjointUnion { b: true } defaults)
  ]
