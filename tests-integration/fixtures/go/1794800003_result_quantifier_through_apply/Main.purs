module Main where

import Prelude

data Tagged :: Type -> Type -> Type
data Tagged tag a = Tagged a

type Untagged a = forall tag. Tagged tag a

tagged :: forall a. a -> Untagged a
tagged = Tagged

untag :: forall a. Tagged Unit a -> a
untag (Tagged a) = a

main :: Array String
main = [ untag (tagged "applied"), untag (tagged $ "through $") ]
