module TL.BuilderOps where

import Prelude

import Data.Array as Array
import Data.Symbol (class IsSymbol)
import Effect (Effect)
import Effect.Console (log)
import Prim.Row as Row
import Record.Builder (Builder, build, buildFromScratch, delete, disjointUnion, insert, merge, modify, nub, rename, union, flip)
import Type.Proxy (Proxy(..))
import Record as Record

renameTo :: forall @from @to a r1 r2 r3. IsSymbol from => IsSymbol to => Row.Cons from a r2 r1 => Row.Lacks from r2 => Row.Cons to a r2 r3 => Row.Lacks to r2 => Builder (Record r1) (Record r3)
renameTo = rename (Proxy @from) (Proxy @to)

pipeline :: Builder { a :: Int, b :: String } { alpha :: Int, b :: String, c :: Boolean, d :: Array Int }
pipeline = renameTo @"a" @"alpha"
  >>> insert (Proxy @"c") true
  >>> merge { d: [ 1 ] }

bumps :: Array (Builder { n :: Int } { n :: Int })
bumps = Array.replicate 5 (modify (Proxy @"n") (_ * 2))

main :: Effect Unit
main = do
  log (show (build pipeline { a: 1, b: "x" }))
  log (show (build (delete (Proxy @"b")) { a: 1, b: "x" }))
  log (show (build (Array.foldl (>>>) identity bumps) { n: 1 }))
  log (show (Record.get (Proxy @"a") (build (union { a: 99, z: "z" }) { a: 1 } :: { a :: Int, a :: Int, z :: String })))
  log (show (build (nub <<< union { a: 99, z: "z" }) { a: 1 }))
  log (show (build (disjointUnion { z: "z" }) { a: 1 }))
  log (show (build (flip merge { a: 5, extra: true }) { a: 1 }))
  log (show (buildFromScratch (insert (Proxy @"only") 1)))
  log (show (build (modify (Proxy @"s") show) { s: 42, t: 1 }))
