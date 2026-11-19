module Bench.Idiom.Number.NBody where

import Prelude

import Bench.Harness (benchmark)
import Data.Array as Array
import Data.FoldableWithIndex (foldlWithIndex)
import Data.Number as Number
import Data.Number.Format (fixed, toStringWith)
import Effect (Effect)

idiom :: String
idiom = "nbody: records of Numbers in an array, advanced by mapWithIndex with an inner foldlWithIndex over the other bodies, sqrt from Data.Number"

main :: Effect Unit
main = benchmark { size: 200000, workload }

type Body = { x :: Number, y :: Number, z :: Number, vx :: Number, vy :: Number, vz :: Number, mass :: Number }

workload :: Int -> String
workload steps = toStringWith (fixed 9) (energy (simulate steps initial))

simulate :: Int -> Array Body -> Array Body
simulate steps = go 0
  where
  go i bodies
    | i >= steps = bodies
    | otherwise = go (i + 1) (advance 0.01 bodies)

advance :: Number -> Array Body -> Array Body
advance dt bodies = map move (Array.mapWithIndex accelerate bodies)
  where
  accelerate i body = foldlWithIndex (pullUnlessSelf i) body bodies

  pullUnlessSelf i j acc other
    | i == j = acc
    | otherwise = do
        let dx = other.x - acc.x
        let dy = other.y - acc.y
        let dz = other.z - acc.z
        let distanceSquared = dx * dx + dy * dy + dz * dz
        let magnitude = dt / (distanceSquared * Number.sqrt distanceSquared)
        acc
          { vx = acc.vx + dx * other.mass * magnitude
          , vy = acc.vy + dy * other.mass * magnitude
          , vz = acc.vz + dz * other.mass * magnitude
          }

  move body = body { x = body.x + dt * body.vx, y = body.y + dt * body.vy, z = body.z + dt * body.vz }

energy :: Array Body -> Number
energy bodies = foldlWithIndex kineticAndPotential 0.0 bodies
  where
  kineticAndPotential i total body = do
    let kinetic = 0.5 * body.mass * (body.vx * body.vx + body.vy * body.vy + body.vz * body.vz)
    foldlWithIndex (potential i body) (total + kinetic) bodies

  potential i body j total other
    | j <= i = total
    | otherwise = do
        let dx = body.x - other.x
        let dy = body.y - other.y
        let dz = body.z - other.z
        total - body.mass * other.mass / Number.sqrt (dx * dx + dy * dy + dz * dz)

initial :: Array Body
initial =
  [ { x: 0.0, y: 0.0, z: 0.0, vx: 0.0, vy: 0.0, vz: 0.0, mass: 39.47841760435743 }
  , { x: 4.84143144246472090, y: -1.16032004402742839, z: -0.103622044471123109, vx: 0.606326392995832, vy: 2.81198684491626, vz: -0.02521836165988763, mass: 0.03769367487038949 }
  , { x: 8.34336671824457987, y: 4.12479856412430479, z: -0.403523417114321381, vx: -1.0107743461787924, vy: 1.8256623712304119, vz: 0.008415761376584154, mass: 0.011286326131968767 }
  , { x: 12.8943695621391310, y: -15.1111514016986312, z: -0.223307578892655734, vx: 1.0827910064415354, vy: 0.8687130181696082, vz: -0.010832637401363636, mass: 0.0017237240570597112 }
  , { x: 15.3796971148509165, y: -25.9193146099879641, z: 0.179258772950371181, vx: 0.979090732243898, vy: 0.5946989986476762, vz: -0.034755955504078104, mass: 0.0020336868699246304 }
  ]
