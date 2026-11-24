module TL.Hetero where

import Prelude

import Data.Maybe (Maybe(..), fromMaybe)
import Data.Symbol (class IsSymbol, reflectSymbol)
import Effect (Effect)
import Effect.Console (log)
import Heterogeneous.Folding (class Folding, class FoldingWithIndex, hfoldl, hfoldlWithIndex)
import Heterogeneous.Mapping (class Mapping, class MappingWithIndex, hmap, hmapWithIndex)
import Data.Tuple.Nested ((/\))
import Data.Variant (Variant, inj)
import Type.Proxy (Proxy(..))

data ShowField = ShowField

instance Show a => Mapping ShowField a String where
  mapping ShowField = show

data WrapJust = WrapJust

instance Mapping WrapJust a (Maybe a) where
  mapping WrapJust = Just

data PrefixWithLabel = PrefixWithLabel

instance (IsSymbol label, Show a) => MappingWithIndex PrefixWithLabel (Proxy label) a String where
  mappingWithIndex PrefixWithLabel label value = reflectSymbol label <> "=" <> show value

data CountFields = CountFields

instance Folding CountFields Int a Int where
  folding CountFields acc _ = acc + 1

data ShowAll = ShowAll

instance (IsSymbol label, Show a) => FoldingWithIndex ShowAll (Proxy label) String a String where
  foldingWithIndex ShowAll label acc value = acc <> "[" <> reflectSymbol label <> ":" <> show value <> "]"

data SumInts = SumInts

instance Folding SumInts Int Int Int where
  folding SumInts acc n = acc + n
else instance Folding SumInts Int a Int where
  folding SumInts acc _ = acc

-- mapping with a closure
newtype AddN = AddN Int

instance Mapping AddN Int Int where
  mapping (AddN n) = (_ + n)
else instance Mapping AddN a a where
  mapping _ = identity

-- fold into Maybe record presence
data AllJust = AllJust

instance Folding AllJust Boolean (Maybe a) Boolean where
  folding AllJust acc m = acc && case m of
    Just _ -> true
    Nothing -> false


main :: Effect Unit
main = do
  let person = { name: "Ann", age: 33, tall: true, score: 1.5 }
  log (show (hmap ShowField person))
  log (show (hmap WrapJust person))
  log (show (hmapWithIndex PrefixWithLabel person))
  log (show (hfoldl CountFields 0 person))
  log (hfoldlWithIndex ShowAll "" person)
  log (show (hfoldl SumInts 0 { a: 1, b: "x", c: 41, d: true }))
  log (show (hmap (AddN 10) { a: 1, b: "x", c: 41 }))
  log (show (hfoldl AllJust true { a: Just 1, b: Just "s" }))
  log (show (hfoldl AllJust true { a: Just 1, b: (Nothing :: Maybe Int) }))
  log (show (hmap ShowField (1 /\ "two")))
  log (show (hmap ShowField { x: [ 1, 2 ] }))
  log (show (hfoldl CountFields 0 {}))
