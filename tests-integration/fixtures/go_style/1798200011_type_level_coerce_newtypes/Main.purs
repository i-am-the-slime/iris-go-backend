module TL.Coerce2 where

import Prelude

import Data.Array as Array
import Data.Variant (Variant, inj)
import Effect (Effect)
import Effect.Console (log)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)
import Record as Record

type Wide = { name :: String, age :: Int, email :: String }

narrow :: forall r. { name :: String | r } -> { name :: String }
narrow = unsafeCoerce

main :: Effect Unit
main = do
  let wide = { name: "Ann", age: 30, email: "a@x" } :: Wide
  log (show (narrow wide))
  log (show (unsafeCoerce wide :: { age :: Int, name :: String }))
  log (show ((unsafeCoerce wide :: { age :: Int, name :: String }) == { age: 30, name: "Ann" }))
  let v = inj (Proxy @"a") 1 :: Variant (a :: Int)
  let vBig = unsafeCoerce v :: Variant (a :: Int, b :: String, c :: Boolean)
  log (show vBig)
  log (show (vBig == inj (Proxy @"a") 1))
  log (show (vBig == inj (Proxy @"b") "x"))
  let manyWide = [ wide, wide { name = "Bo" } ]
  log (show (unsafeCoerce manyWide :: Array { name :: String }))
  log (show (Array.length (unsafeCoerce manyWide :: Array { email :: String })))
  log (show (Record.get (Proxy @"email") (unsafeCoerce (narrow wide) :: { email :: String })))
  let updated = (unsafeCoerce wide :: { age :: Int }) { age = 31 }
  log (show updated)
