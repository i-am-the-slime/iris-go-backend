module Main where

import Prelude

import Data.Either (Either(..), either)
import Data.Void (Void, absurd)
import Unsafe.Coerce (unsafeCoerce)

data Val

newtype Box a = Box Val

box :: forall a. a -> Box a
box a = Box (unsafeCoerce a)

unbox :: forall a. Box a -> a
unbox (Box value) = unsafeCoerce value

never :: Box Void -> String
never = absurd <<< unbox

describe :: Either String (Box Void) -> String
describe = either identity never

main :: Array String
main = [ show (unbox (box 1) + 1) ] <> map describe [ Left "no", Left "void" ]
