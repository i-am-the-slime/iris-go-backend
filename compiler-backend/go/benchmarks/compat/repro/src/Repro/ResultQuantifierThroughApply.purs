module Repro.ResultQuantifierThroughApply where

import Prelude

import Effect (Effect)
import Effect.Console (log)

data Tagged :: Type -> Type -> Type
data Tagged tag a = Tagged a

type Untagged a = forall tag. Tagged tag a

tagged :: forall a. a -> Untagged a
tagged = Tagged

untag :: forall a. Tagged Unit a -> a
untag (Tagged a) = a

main :: Effect Unit
main = do
  log (untag (tagged "applied"))
  log (untag (tagged $ "through $"))
