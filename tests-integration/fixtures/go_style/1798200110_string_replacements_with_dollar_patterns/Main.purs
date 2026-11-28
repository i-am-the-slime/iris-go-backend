module Repro.R10 where

import Prelude

import Data.Foldable (for_)
import Data.String as String
import Data.String.Pattern (Pattern(..), Replacement(..))
import Data.String.Regex as Regex
import Data.String.Regex.Flags (global)
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = do
  for_ [ "[$&]", "$$", "$`", "$'", "$1", "$" ] \replacement -> do
    log $ replacement <> " replace    " <> String.replace (Pattern "an") (Replacement replacement) "banana"
    log $ replacement <> " replaceAll " <> String.replaceAll (Pattern "an") (Replacement replacement) "banana"
    for_ (Regex.regex "(an)" global) \re -> log (replacement <> " regex      " <> Regex.replace re replacement "banana")
