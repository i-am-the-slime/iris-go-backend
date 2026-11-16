module Main where

import Prelude

-- `Algebra` quantifies a row, `ops`. Passed as an `Algebra`, `measure` is instantiated at the
-- skolems of that `forall`, which is erased with them: `ops` drops out of the record, which keeps
-- the field `measure` can read.

type Operations node ops = (recurse :: node -> node | ops)

type Algebra = forall node ops. (node -> Int) -> Record (Operations node ops) -> node -> Int

measure :: Algebra
measure size operations node = size (operations.recurse node)

withLayer :: Algebra -> Int -> Int
withLayer algebra start = algebra identity { recurse: (_ + 1), layer: \n -> n * 2 } start

main :: Array String
main = map (show <<< withLayer measure) [ 20, 41 ]
