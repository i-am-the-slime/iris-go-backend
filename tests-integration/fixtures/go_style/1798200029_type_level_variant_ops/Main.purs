module TL.VariantOps where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Symbol (class IsSymbol, reflectSymbol)
import Data.Variant (Unvariant(..), Variant, contract, default, expand, inj, on, onMatch, over, overOne, overSome, prj, revariant, traverse, traverseOne, unvariant, case_)
import Effect (Effect)
import Effect.Console (log)
import Prim.Row as Row
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

type Shape = (circle :: Number, square :: Int, label :: String)

injAs :: forall @label a r1 r2. IsSymbol label => Row.Cons label a r1 r2 => a -> Variant r2
injAs = inj (Proxy @label)

-- polymorphic over an open variant
circleArea :: forall r. Variant (circle :: Number | r) -> Maybe Number
circleArea = default Nothing # on (Proxy @"circle") (\radius -> Just (radius * radius * 3.0))

describe :: forall r. Variant (circle :: Number, square :: Int | r) -> String
describe = default "unknown"
  # on (Proxy @"circle") (\r -> "circle " <> show r)
  # on (Proxy @"square") (\s -> "square " <> show s)

doubled :: Variant Shape -> Variant Shape
doubled = over { circle: (_ * 2.0), square: (_ * 2) }

doubledSome :: Variant Shape -> Variant (circle :: Number, square :: Int, label :: String)
doubledSome = overSome { circle: (_ * 2.0) } expand

labelName :: forall r. Variant r -> String
labelName v = unvariant v # \(Unvariant run) -> run \proxy _ -> reflectSymbol proxy

traversed :: Variant Shape -> Maybe (Variant Shape)
traversed = traverse { circle: \c -> if c > 0.0 then Just c else Nothing }

main :: Effect Unit
main = do
  let circle = injAs @"circle" 1.5 :: Variant Shape
  let square = injAs @"square" 3 :: Variant Shape
  let label = injAs @"label" "hi" :: Variant Shape
  log (show (circleArea circle))
  log (show (circleArea square))
  log (show (circleArea (injAs @"circle" 2.0 :: Variant (circle :: Number))))
  log (describe label)
  log (describe circle)
  log (describe (injAs @"square" 9 :: Variant (square :: Int, circle :: Number, other :: Unit)))
  log (show (doubled circle))
  log (show (doubled square))
  log (show (doubled label))
  log (show (doubledSome circle))
  log (show (overOne (Proxy @"label") (_ <> "!") expand label :: Variant Shape))

  log (show (contract circle :: Maybe (Variant (circle :: Number))))
  log (show (contract label :: Maybe (Variant (circle :: Number, square :: Int))))
  log (show (traversed circle))
  log (show (traversed (injAs @"circle" (-1.0))))
  log (show (traversed square))
  log (show (traverseOne (Proxy @"square") (\n -> [ n, n + 1 ]) (pure <<< expand) square :: Array (Variant Shape)))
  log (show (prj (Proxy @"label") label :: Maybe String))
  log (show (expand (injAs @"a" 1 :: Variant (a :: Int)) :: Variant (a :: Int, b :: Int)))
