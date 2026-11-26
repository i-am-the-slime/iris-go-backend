module Box where

foreign import data Box :: Type -> Type

foreign import put :: forall a. a -> Box a

foreign import get :: forall a. Box a -> a

foreign import sealed :: forall a. a -> Box Int
