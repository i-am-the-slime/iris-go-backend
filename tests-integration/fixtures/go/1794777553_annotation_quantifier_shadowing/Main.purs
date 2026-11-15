module Main where

import Prelude

import Data.Array as Array
import Data.List (List)
import Data.Tuple (Tuple(..), snd)

-- `conv`'s `m ~> m'` binds `a`, and so does the annotation `List ~> List` in its body. The
-- annotation's `a` is instantiated at `Tuple String a`, not at `conv`'s own `a`.

labelled :: forall a. Array a -> List (Tuple String a)
labelled = Array.toUnfoldable <<< map (Tuple "label")

conv :: Array ~> Array
conv = labelled >>> (identity :: List ~> List) >>> Array.fromFoldable >>> map snd

main :: Array String
main = map show (conv [ true, false ]) <> conv [ "kept" ]
