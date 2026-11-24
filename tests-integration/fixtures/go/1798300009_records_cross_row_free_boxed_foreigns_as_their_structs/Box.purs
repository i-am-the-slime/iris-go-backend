module Box (Box, newBox, readBox) where

foreign import data Box :: Type -> Type

foreign import newBox :: forall a. a -> Box a

foreign import readBox :: forall a. Box a -> a
