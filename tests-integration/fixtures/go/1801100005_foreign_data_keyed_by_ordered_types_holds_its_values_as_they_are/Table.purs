module Table (Table, empty, lookup, insert, values) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)

foreign import data Table :: Type -> Type -> Type

foreign import empty :: forall k v. Effect (Table k v)

lookup :: forall k v. k -> Table k v -> Effect (Maybe v)
lookup = lookupImpl Just Nothing

foreign import lookupImpl :: forall k v. (v -> Maybe v) -> Maybe v -> k -> Table k v -> Effect (Maybe v)

foreign import insert :: forall k v. k -> v -> Table k v -> Effect Unit

foreign import values :: forall k v. Table k v -> Effect (Array v)
