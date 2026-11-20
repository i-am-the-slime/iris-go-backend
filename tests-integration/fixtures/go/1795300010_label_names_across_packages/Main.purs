module Main where

import Prelude

import Data.Array (length)
import Data.Variant (inj)
import Labels (describe, lower, odd, respondNow, upper)
import Type.Proxy (Proxy(..))

-- | Every label has an exported Go name, so records and variants built in one module work in
-- | another: a leading `_`, a digit first, a quoted label, letters beyond ASCII, and labels whose
-- | Go names would be the same.
main :: Array String
main = do
  let record = odd 1
  let updated = record { _respondNow = 10, "content-type" = "changed" }
  let replies = [ respondNow 7, lower 1, upper 2, inj (Proxy :: Proxy "later") "soon" ]
  map describe replies <>
    [ show [ updated._respondNow, updated."1st", updated.x, updated."X", updated.über ]
    , updated."content-type" <> " " <> updated.content_type
    , show (length replies)
    ]
