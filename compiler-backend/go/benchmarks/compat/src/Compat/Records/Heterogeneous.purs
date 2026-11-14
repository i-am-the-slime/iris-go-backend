module Compat.Records.Heterogeneous where

import Prelude

import Data.Symbol (class IsSymbol, reflectSymbol)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Console (log)
import Heterogeneous.Folding (class FoldingWithIndex, hfoldlWithIndex, class Folding, hfoldl)
import Heterogeneous.Mapping (class Mapping, class MappingWithIndex, hmap, hmapWithIndex)
import Type.Proxy (Proxy)

data ShowField = ShowField

instance Show a => Mapping ShowField a String where
  mapping ShowField = show

data Labelled = Labelled

instance (IsSymbol label, Show a) => MappingWithIndex Labelled (Proxy label) a String where
  mappingWithIndex Labelled label value = reflectSymbol label <> "=" <> show value

data Describe = Describe

instance (IsSymbol label, Show a) => FoldingWithIndex Describe (Proxy label) String a String where
  foldingWithIndex Describe label accumulated value = accumulated <> "[" <> reflectSymbol label <> ":" <> show value <> "]"

data Count = Count

instance Folding Count Int a Int where
  folding Count total _ = total + 1

main :: Effect Unit
main = do
  let config = { port: 8080, host: "localhost", debug: true, ratio: 0.5 }
  let shown = hmap ShowField config
  log (shown.port <> " " <> shown.host <> " " <> shown.debug <> " " <> shown.ratio)
  let labelled = hmapWithIndex Labelled config
  log (labelled.debug <> ", " <> labelled.host)
  log (hfoldlWithIndex Describe "" config)
  log (show (hfoldl Count 0 config))
  log (show (hmap ShowField (1 /\ "two")))
