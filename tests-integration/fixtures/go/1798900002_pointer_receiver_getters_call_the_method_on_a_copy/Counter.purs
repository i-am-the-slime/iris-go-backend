module Counter where

foreign import data Counter :: Type

foreign import zero :: Counter

foreign import bumped :: Counter -> Int

foreign import count :: Counter -> Int
