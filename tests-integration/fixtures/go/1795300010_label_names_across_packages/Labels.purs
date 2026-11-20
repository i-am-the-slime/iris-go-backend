module Labels where

import Prelude

import Data.Variant (Variant, case_, inj, on)
import Type.Proxy (Proxy(..))

type Odd =
  { _respondNow :: Int
  , "1st" :: Int
  , "content-type" :: String
  , content_type :: String
  , x :: Int
  , "X" :: Int
  , über :: Int
  }

odd :: Int -> Odd
odd n =
  { _respondNow: n
  , "1st": n + 1
  , "content-type": "dash"
  , content_type: "underscore"
  , x: n * 2
  , "X": n * 3
  , über: n * 4
  }

type Reply = Variant (_respondNow :: Int, later :: String, a :: Int, "A" :: Int)

respondNow :: Int -> Reply
respondNow = inj (Proxy :: Proxy "_respondNow")

lower :: Int -> Reply
lower = inj (Proxy :: Proxy "a")

upper :: Int -> Reply
upper = inj (Proxy :: Proxy "A")

describe :: Reply -> String
describe = case_
  # on (Proxy :: Proxy "_respondNow") (\n -> "now " <> show n)
  # on (Proxy :: Proxy "later") (\text -> "later " <> text)
  # on (Proxy :: Proxy "a") (\n -> "a " <> show n)
  # on (Proxy :: Proxy "A") (\n -> "A " <> show n)
