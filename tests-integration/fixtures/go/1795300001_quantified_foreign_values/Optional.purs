module Optional where

import Effect (Effect)

foreign import data Optional :: Type -> Type

foreign import data Pair :: Type -> Type -> Type

foreign import absent :: forall a. Optional a

foreign import present :: forall a. a -> Optional a

foreign import withDefault :: forall a. a -> Optional a -> a

foreign import emptyArray :: forall a. Array a

foreign import swappedPair :: forall a b. a -> b -> Pair b a

foreign import emptySwappedPair :: forall a b. Pair b a

foreign import pairSize :: forall a b. Pair a b -> Int

foreign import newCounter :: forall a. Effect (Optional a)
