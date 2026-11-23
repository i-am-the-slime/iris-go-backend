module Main where

import Prelude

import Data.Either (either)
import Data.String.CodeUnits as String
import Data.String.Unsafe as Unsafe
import Data.Char (toCharCode)
import Effect (Effect)
import Effect.Exception (try)
import Effect.Ref (Ref)
import Effect.Ref as Ref

addCodes :: Ref Int -> String -> Int -> Effect Unit
addCodes total text index
  | index > String.length text = pure unit
  | otherwise = do
      Ref.modify_ (_ + toCharCode (Unsafe.charAt index text)) total
      addCodes total text (index + 1)

main :: Effect Int
main = do
  total <- Ref.new 0
  failed <- either (const 1) (const 0) <$> try (addCodes total "abc" 0)
  read <- Ref.read total
  pure (read + failed)
