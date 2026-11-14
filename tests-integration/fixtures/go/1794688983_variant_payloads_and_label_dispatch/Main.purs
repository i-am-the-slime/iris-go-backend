module Main where

import Prelude

import Data.Variant (Variant, case_, default, inj, match, on, onMatch)
import Record.Studio.Shrink (shrink)
import Type.Proxy (Proxy(..))

type Problems = (missing :: String, invalid :: Int, late :: { after :: Int })

-- `on` reads each payload at its own type only under its own label.
byLabel :: Variant Problems -> String
byLabel = case_
  # on (Proxy :: Proxy "missing") (\name -> "missing " <> name)
  # on (Proxy :: Proxy "invalid") (\code -> "invalid " <> show code)
  # on (Proxy :: Proxy "late") (\{ after } -> "late " <> show after)

-- `match` and `onMatch` choose a handler from a record by the run-time label.
byRecord :: Variant Problems -> String
byRecord = match
  { missing: \name -> "no " <> name
  , invalid: \code -> "bad " <> show (code * 2)
  , late: \{ after } -> "after " <> show after
  }

someLabels :: Variant Problems -> String
someLabels = onMatch { invalid: \code -> show (code + 1) } (default "unhandled")

problems :: Array (Variant Problems)
problems =
  [ inj (Proxy :: Proxy "missing") "user"
  , inj (Proxy :: Proxy "invalid") 3
  , inj (Proxy :: Proxy "late") { after: 5 }
  ]

-- `shrink` keeps the fields its result type names.
shrunk :: { base :: Int, name :: String }
shrunk = shrink { base: 1, name: "context", scale: 2 }

main :: Array String
main = map byLabel problems <> map byRecord problems <> map someLabels problems <> [ shrunk.name <> show shrunk.base ]
