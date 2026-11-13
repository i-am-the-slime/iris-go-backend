module CompactionDriver where

import Prelude

import Data.Array as Array
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Newtype (un)
import Data.String.Common (joinWith)
import Data.Tuple (Tuple)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Console (log)
import LayeredLayout.Compaction.HorizontalGraphCompactor as Compactor
import LayeredLayout.Graph (EdgeId(..), Label(..), NodeId(..), PortId(..), Side(..))
import LayeredLayout.Grid (GridPos(..), GridSize(..))
import LayeredLayout.Result (BendType(..), Direction(..))

main :: Effect Unit
main = do
  log (compaction twoNodes)
  log (compaction diamond)
  where
  compaction input = do
    let result = Compactor.compactPostRouting Compactor.EdgeLength Compactor.defaultWithinLayerSpacings Compactor.defaultBetweenLayersSpacings input
    object
      [ "input" /\ graph input.nodes input.edges input.paths input.ports
      , "output" /\ graph result.nodes input.edges result.edges input.ports
      , "boundingBox" /\ object [ "pos" /\ position result.boundingBox.pos, "size" /\ size result.boundingBox.size ]
      ]

  graph nodes edges paths ports = object
    [ "nodes" /\ array (map node nodes)
    , "edges" /\ array (map edge edges)
    , "paths" /\ array (map path paths)
    , "ports" /\ array (map portsOf (Map.toUnfoldable ports))
    ]

  node n = object
    [ "node" /\ string (un NodeId n.node)
    , "layer" /\ show n.layer
    , "order" /\ show n.order
    , "position" /\ position n.position
    , "size" /\ size n.size
    ]

  edge e = object
    [ "id" /\ string (un EdgeId e.id)
    , "from" /\ endpoint e.from
    , "to" /\ endpoint e.to
    , "label" /\ maybe (string <<< un Label) e.label
    ]

  endpoint e = object [ "node" /\ string (un NodeId e.node), "port" /\ maybe (string <<< un PortId) e.port ]

  path p = object
    [ "edge" /\ string (un EdgeId p.edge)
    , "bendType" /\ array (map (string <<< bendType) p.bendType)
    , "bends" /\ array (map position p.bends)
    , "jumps" /\ array (map (\j -> object [ "crossingEdge" /\ string (un EdgeId j.crossingEdge), "position" /\ position j.position ]) p.jumps)
    , "reversed" /\ show p.reversed
    , "segments" /\ array (map segment p.segments)
    ]

  segment s = object
    [ "direction" /\ string (direction s.direction)
    , "start" /\ position s.start
    , "end" /\ position s.end
    ]

  portsOf (nodeId /\ nodePorts) = object
    [ "node" /\ string (un NodeId nodeId)
    , "ports" /\ array (map port nodePorts)
    ]

  port p = object
    [ "id" /\ string (un PortId p.id)
    , "label" /\ maybe string p.label
    , "offset" /\ show p.offset
    , "side" /\ string (side p.side)
    ]

  position (GridPos (x /\ y)) = array [ show x, show y ]
  size (GridSize (width /\ height)) = array [ show width, show height ]

  direction H = "H"
  direction V = "V"

  bendType LeftTurn = "LeftTurn"
  bendType RightTurn = "RightTurn"

  side North = "North"
  side South = "South"
  side East = "East"
  side West = "West"


maybe :: forall a. (a -> String) -> Maybe a -> String
maybe render = case _ of
  Just value -> render value
  Nothing -> "null"

string :: String -> String
string = show

array :: Array String -> String
array elements = "[" <> joinWith "," elements <> "]"

object :: Array (Tuple String String) -> String
object fields = "{" <> joinWith "," (map (\(key /\ value) -> show key <> ":" <> value) fields) <> "}"

twoNodes =
  { nodes:
      [ { node: NodeId "a", layer: 0, order: 0, position: point 0.0 0.0, size: extent 4.0 4.0 }
      , { node: NodeId "b", layer: 1, order: 0, position: point 20.0 12.0, size: extent 4.0 4.0 }
      ]
  , edges: [ { id: EdgeId "e", from: { node: NodeId "a", port: Nothing }, to: { node: NodeId "b", port: Nothing }, label: Nothing } ]
  , paths:
      [ { edge: EdgeId "e"
        , bendType: []
        , bends: [ point 4.0 2.0, point 18.0 14.0 ]
        , jumps: []
        , reversed: false
        , segments:
            [ { direction: H, start: point 2.0 2.0, end: point 10.0 2.0 }
            , { direction: V, start: point 10.0 2.0, end: point 10.0 14.0 }
            , { direction: H, start: point 10.0 14.0, end: point 20.0 14.0 }
            ]
        }
      ]
  , ports: Map.empty
  , tailLabelOwners: Map.empty
  }

diamond =
  { nodes:
      [ { node: NodeId "top", layer: 0, order: 0, position: point 0.0 10.0, size: extent 6.0 4.0 }
      , { node: NodeId "left", layer: 1, order: 0, position: point 30.0 0.0, size: extent 4.0 6.0 }
      , { node: NodeId "right", layer: 1, order: 1, position: point 30.0 24.0, size: extent 4.0 6.0 }
      , { node: NodeId "bottom", layer: 2, order: 0, position: point 60.0 10.0, size: extent 6.0 4.0 }
      ]
  , edges:
      [ { id: EdgeId "tl", from: { node: NodeId "top", port: Just (PortId "out") }, to: { node: NodeId "left", port: Nothing }, label: Just (Label "go") }
      , { id: EdgeId "tr", from: { node: NodeId "top", port: Nothing }, to: { node: NodeId "right", port: Nothing }, label: Nothing }
      , { id: EdgeId "lb", from: { node: NodeId "left", port: Nothing }, to: { node: NodeId "bottom", port: Nothing }, label: Nothing }
      , { id: EdgeId "rb", from: { node: NodeId "right", port: Nothing }, to: { node: NodeId "bottom", port: Nothing }, label: Nothing }
      ]
  , paths:
      [ route "tl" [ point 6.0 12.0, point 18.0 12.0, point 18.0 3.0, point 30.0 3.0 ]
      , route "tr" [ point 6.0 12.0, point 20.0 12.0, point 20.0 27.0, point 30.0 27.0 ]
      , route "lb" [ point 34.0 3.0, point 46.0 3.0, point 46.0 12.0, point 60.0 12.0 ]
      , route "rb" [ point 34.0 27.0, point 48.0 27.0, point 48.0 12.0, point 60.0 12.0 ]
      ]
  , ports: Map.singleton (NodeId "top") [ { id: PortId "out", side: East, offset: 2, label: Just "out" } ]
  , tailLabelOwners: Map.empty
  }
  where
  route name points =
    { edge: EdgeId name
    , bendType: [ LeftTurn, RightTurn ]
    , bends: Array.slice 1 (Array.length points - 1) points
    , jumps: []
    , reversed: false
    , segments: Array.zipWith segmentBetween points (Array.drop 1 points)
    }
  segmentBetween start@(GridPos (x /\ _)) end@(GridPos (x' /\ _)) =
    { direction: if x == x' then V else H, start, end }

point :: Number -> Number -> GridPos
point x y = GridPos (x /\ y)

extent :: Number -> Number -> GridSize
extent width height = GridSize (width /\ height)
