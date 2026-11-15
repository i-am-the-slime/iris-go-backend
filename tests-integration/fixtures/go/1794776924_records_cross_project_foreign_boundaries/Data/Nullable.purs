module Data.Nullable where

foreign import data Nullable :: Type -> Type

foreign import nullable :: forall a r. Nullable a -> r -> (a -> r) -> r
