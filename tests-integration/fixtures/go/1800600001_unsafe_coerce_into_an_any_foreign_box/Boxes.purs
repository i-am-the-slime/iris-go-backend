module Boxes (Box, intoBox, outOfBox) where

import Unsafe.Coerce (unsafeCoerce)

foreign import data Box :: Type

intoBox :: forall a. a -> Box
intoBox = unsafeCoerce

outOfBox :: forall a. Box -> a
outOfBox = unsafeCoerce
