module Main where

import Prelude

import Data.Foldable (foldl)
import Effect (Effect)
import Effect.Ref as Ref
import Foreign.Object as Object
import Journal (log)

main :: Effect Unit
main = do
  cancellers <- Ref.new (Object.singleton "a" (log "cancel a"))
  Ref.modify_ (Object.insert "b" (log "cancel b")) cancellers
  Ref.read cancellers >>= foldl (*>) (pure unit)
  log "done"
