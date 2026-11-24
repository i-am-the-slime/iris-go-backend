module TL.Studio where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Symbol (class IsSymbol, reflectSymbol)
import Data.Variant (Variant, inj, match, onMatch, on, case_, default)
import Data.Functor.Variant (VariantF)
import Data.Functor.Variant as VF
import Effect (Effect)
import Effect.Console (log)
import Prim.Row as Row
import Prim.RowList as RL
import Record.Studio (mapRecord, sequenceRecord, mapRecordKind, recordKeys, shrink, mapUniformRecord, (//), key, value)
import Type.Proxy (Proxy(..))

-- Router style: handlers record keyed by route label, dispatcher from Variant
type Routes = (home :: Unit, user :: Int, search :: { q :: String, page :: Int })

handlers :: { home :: Unit -> String, user :: Int -> String, search :: { q :: String, page :: Int } -> String }
handlers =
  { home: \_ -> "home"
  , user: \id -> "user #" <> show id
  , search: \{ q, page } -> "search " <> q <> " p" <> show page
  }

dispatch :: Variant Routes -> String
dispatch = match handlers

-- VariantF
type Effects a = VariantF (maybe :: Maybe, either :: Either String, array :: Array) a

describeF :: Effects Int -> String
describeF = VF.match
  { maybe: \m -> "maybe " <> show m
  , either: \e -> "either " <> show e
  , array: \xs -> "array " <> show xs
  }

main :: Effect Unit
main = do
  log (show (mapRecord (_ * 2) { a: 1, b: 2, c: 3 }))
  log (show (sequenceRecord { a: Just 1, b: Just "x" } :: Maybe { a :: Int, b :: String }))
  log (show (sequenceRecord { a: Just 1, b: (Nothing :: Maybe String) } :: Maybe { a :: Int, b :: String }))
  log (show (sequenceRecord { a: [ 1, 2 ], b: [ "x", "y" ] } :: Array { a :: Int, b :: String }))
  log (show (mapRecordKind Array.head { a: [ 1 ], b: [ "s" ], c: ([] :: Array Boolean) }))
  log (show (recordKeys { zed: 1, alpha: "a" }))
  log (show (shrink { a: 1, b: "x", c: true } :: { a :: Int, c :: Boolean }))
  log (show (mapUniformRecord show { a: 1, b: 2 }))
  log (show ({ a: 1, b: 2 } // { b: "override", c: true }))
  log (reflectSymbol (key { onlyField: 42 }))
  log (dispatch (inj (Proxy @"home") unit))
  log (dispatch (inj (Proxy @"user") 7))
  log (dispatch (inj (Proxy @"search") { q: "cats", page: 2 }))
  log (describeF (VF.inj (Proxy @"maybe") (Just 1)))
  log (describeF (VF.inj (Proxy @"either") (Left "bad")))
  log (describeF (map (_ + 1) (VF.inj (Proxy @"array") [ 1, 2, 3 ])))
  log (describeF (map (_ * 10) (VF.inj (Proxy @"either") (Right 4))))
