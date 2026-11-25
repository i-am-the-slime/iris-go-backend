module Entries (joinEntriesImpl) where

import Data.Function.Uncurried (Fn3)

foreign import joinEntriesImpl
  :: forall f
   . Fn3
       (forall x y. f x y -> x)
       (forall x y. f x y -> y)
       (Array (f String Int))
       String
