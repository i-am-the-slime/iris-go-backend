module Main where

import Prelude

newtype Run r a = Run (forall answer. r -> (a -> answer) -> answer)

data Layer r a = Layer (Run r a)

newtype Scope = Scope Int

build :: forall r a. Layer r a -> Run r a
build (Layer run) = run

runWith :: forall r a. r -> Run r a -> a
runWith environment (Run continue) = continue environment identity

measured :: forall r a. r -> Run r a -> (a -> Int) -> Int
measured environment (Run continue) size = continue environment size

scoped :: Layer Scope String
scoped = Layer (Run \(Scope depth) done -> done ("depth " <> show depth))

labelled :: Layer { scope :: Scope, label :: String } String
labelled = Layer (Run \{ scope: Scope depth, label } done -> done (label <> " " <> show depth))

main :: Array String
main =
  [ runWith (Scope 3) (build scoped)
  , show (measured (Scope 4) (build scoped) (const 7))
  , runWith { scope: Scope 5, label: "outer" } (build labelled)
  ]
