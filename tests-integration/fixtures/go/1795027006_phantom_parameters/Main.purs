module Main where

import Prelude

import Unsafe.Coerce (unsafeCoerce)

data Step tag = Step Int (Int -> Step tag) | Done Int

data Hidden

hide :: Step Int -> Hidden
hide = unsafeCoerce

reveal :: Hidden -> Step Unit
reveal = unsafeCoerce

countdown :: Int -> Step Int
countdown 0 = Done 0
countdown n = Step n countdown

run :: Step Unit -> Int
run (Done total) = total
run (Step n next) = n + run (next (n - 1))

main :: Array Int
main = [ run (reveal (hide (countdown 3))) ]
