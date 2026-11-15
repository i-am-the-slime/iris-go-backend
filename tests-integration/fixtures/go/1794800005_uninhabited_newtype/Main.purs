module Main where

import Prelude

newtype Never = Never Never

absurd :: forall a. Never -> a
absurd (Never never) = absurd never

data Step = Done Int | Impossible Never

value :: Step -> Int
value (Done n) = n
value (Impossible never) = absurd never

steps :: Array Step
steps = [ Done 7, Done 8 ]

main :: Array Int
main = map value steps
