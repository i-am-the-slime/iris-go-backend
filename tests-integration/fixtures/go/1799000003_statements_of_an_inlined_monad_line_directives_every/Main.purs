module Main where

import Prelude

import Effect (Effect)
import Effect.Exception (throw)
import Effect.Ref as Ref
import Hooks (component, useKey, useState)

main :: Effect Unit
main = do
  component 2 \_ -> do
    count <- useState 0
    label <- useState "start"
    let whenPositive action = Ref.read count >>= \current -> when (current > 0) action
    useKey 1 (whenPositive (Ref.write 5 count))
    useKey 2 do
      Ref.modify_ (_ + 1) count
      Ref.write "moved" label
    useKey 2 (Ref.modify_ (_ + 10) count)
    useKey 3 (Ref.modify_ (_ - 1) count)
    final <- useState unit
    useKey 2 do
      total <- Ref.read count
      when (total /= 11) do
        throw "the count is wrong"
      Ref.write unit final
