module Main where

import Prelude

import Record.Builder as Builder
import Type.Proxy (Proxy(..))

main :: { name :: String, size :: Int, tags :: Array String }
main = Builder.build builder { label: "box", size: 1, draft: true }
  where
  builder =
    Builder.insert (Proxy :: _ "tags") [ "new" ]
      >>> Builder.modify (Proxy :: _ "size") (_ + 1)
      >>> Builder.rename (Proxy :: _ "label") (Proxy :: _ "name")
      >>> Builder.delete (Proxy :: _ "draft")
