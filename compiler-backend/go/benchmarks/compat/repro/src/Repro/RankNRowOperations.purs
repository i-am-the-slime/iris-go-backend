module Repro.RankNRowOperations where

import Prelude

import Effect (Effect)
import Effect.Console (log)

type Operations node ops = ( recurse :: node -> node | ops )

type Algebra = forall node ops. (node -> Int) -> Record (Operations node ops) -> node -> Int

measure :: Algebra
measure size operations node = size (operations.recurse node)

withLayer :: Algebra -> Int
withLayer algebra = algebra identity { recurse: (_ + 1), layer: \n -> n * 2 } 20

main :: Effect Unit
main = log (show (withLayer measure))
