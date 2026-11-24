module T.Var where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Symbol (class IsSymbol, reflectSymbol)
import Data.Variant (Variant, case_, default, expand, inj, match, on, onMatch, prj)
import Effect (Effect)
import Effect.Console (log)
import Prim.Row as Row
import Type.Proxy (Proxy(..))

type Shape = Variant (circle :: Number, rect :: { w :: Int, h :: Int }, point :: Unit)
type MoreShape = Variant (circle :: Number, rect :: { w :: Int, h :: Int }, point :: Unit, label :: String)

injAt :: forall @sym a r1 r2. Row.Cons sym a r1 r2 => IsSymbol sym => a -> Variant r2
injAt = inj (Proxy @sym)

onAt :: forall @sym a b r1 r2. Row.Cons sym a r1 r2 => IsSymbol sym => (a -> b) -> (Variant r1 -> b) -> Variant r2 -> b
onAt = on (Proxy @sym)

symbolName :: forall @sym. IsSymbol sym => String
symbolName = reflectSymbol (Proxy @sym)

shapes :: Array Shape
shapes = [ injAt @"circle" 1.5, injAt @"rect" { w: 2, h: 3 }, injAt @"point" unit, inj (Proxy :: _ "circle") (-0.25) ]

area :: Shape -> Number
area = case_
  # onAt @"circle" (\r -> r * r * 3.0)
  # onAt @"rect" (\{ w, h } -> toNumberI (w * h))
  # onAt @"point" (const 0.0)
  where
  toNumberI n = if n == 0 then 0.0 else 1.0 + toNumberI (n - 1)

describe :: Shape -> String
describe = match
  { circle: \r -> "circle " <> show r
  , rect: \r -> "rect " <> show r
  , point: \_ -> "point"
  }

isCircle :: Shape -> Boolean
isCircle = default false # on (Proxy :: _ "circle") (const true)

describeMore :: MoreShape -> String
describeMore = onMatch { label: \s -> "label " <> s } (describe)

main :: Effect Unit
main = do
  shapes <#> area # show # log
  shapes <#> describe # show # log
  shapes <#> isCircle # show # log
  shapes <#> show # Array.intercalate " | " # log
  log (show (shapes == shapes) <> show (Array.sort shapes) <> show (compare (injAt @"circle" 1.0 :: Shape) (injAt @"rect" { w: 0, h: 0 })))
  shapes <#> (prj (Proxy :: _ "rect") :: Shape -> Maybe _) # show # log
  let more = (shapes <#> expand) <> [ injAt @"label" "hi" ] :: Array MoreShape
  more <#> describeMore # show # log
  log (symbolName @"hello" <> symbolName @"" <> symbolName @"ünï cödé")
  log (show (prj (Proxy @"circle") (Array.head shapes # maybe' (injAt @"point" unit)) :: Maybe Number))
  where
  maybe' fallback = case _ of
    Nothing -> fallback
    Just a -> a
