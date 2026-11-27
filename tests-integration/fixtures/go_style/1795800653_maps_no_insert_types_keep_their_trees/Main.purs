module Fun.Untyped where

import Prelude

import Data.Array as Array
import Data.Int (toNumber)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = do
  log "-- a map of a type that nothing inserts into is only read, as a tree"
  log (show (outDegreeCentrality graph))

type SimpleGraph node = { nodes :: Array node, edges :: Map node (Set node) }

graph :: SimpleGraph Int
graph = { nodes: [ 1, 2, 3 ], edges: Map.fromFoldable [ Tuple 1 (targets [ 2, 3 ]), Tuple 2 (targets [ 3 ]) ] }

-- | The keys of a map, which a set of them shares without inserting any.
targets :: Array Int -> Set Int
targets nodes = Map.keys (Map.fromFoldable (nodes <#> \node -> Tuple node "edge"))

outDegreeCentrality :: forall node. Ord node => SimpleGraph node -> Map node Number
outDegreeCentrality graph =
  let
    n = Array.length graph.nodes
    normalizer = if n <= 1 then 1.0 else toNumber (n - 1)
  in
    Map.fromFoldable $ graph.nodes <#> \node ->
      let outDeg = case Map.lookup node graph.edges of
            Nothing -> 0
            Just targets -> Set.size targets
      in Tuple node (toNumber outDeg / normalizer)
