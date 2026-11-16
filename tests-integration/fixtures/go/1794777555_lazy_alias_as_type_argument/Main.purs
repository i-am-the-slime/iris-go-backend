module Main where

import Prelude

import Data.Lazy (Lazy, defer, force)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))

-- `Stream` is the alias `*lazy.Lazy[TupleLabelledLazyStream]`. `Labelled`, declared first, holds
-- a `Stream`, and the tuple holds a `Lazy Stream`. Go cannot instantiate `lazy.Lazy` at the alias
-- while it is still declaring it (go.dev/issue/78296), so the tuple's field spells it out.

data Labelled = Labelled String (Maybe Stream)

newtype Stream = Stream (Lazy (Tuple Labelled (Lazy Stream)))

from :: Int -> Stream
from n = Stream (defer \_ -> Tuple (Labelled (show n) Nothing) (defer \_ -> from (n + 1)))

take :: Int -> Stream -> Array String
take 0 _ = []
take n (Stream cell) = case force cell of
  Tuple (Labelled label _) rest -> [ label ] <> take (n - 1) (force rest)

main :: Array String
main = take 3 (from 1)
