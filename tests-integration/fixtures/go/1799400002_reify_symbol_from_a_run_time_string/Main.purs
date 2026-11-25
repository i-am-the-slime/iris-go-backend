module Main where

import Prelude

import Data.Foldable (for_)
import Data.Symbol (class IsSymbol, reflectSymbol, reifySymbol)
import Effect (Effect)
import Journal (log)
import Type.Proxy (Proxy(..))

greeting :: forall label. IsSymbol label => Proxy label -> String
greeting label = "hello " <> reflectSymbol label

shouted :: forall label. IsSymbol label => Proxy label -> String
shouted label = greeting label <> "!" <> reflectSymbol (Proxy :: Proxy "known")

main :: Effect Unit
main = for_ [ "world", "there" ] \name -> do
  log (reifySymbol name greeting)
  log (reifySymbol name shouted)
