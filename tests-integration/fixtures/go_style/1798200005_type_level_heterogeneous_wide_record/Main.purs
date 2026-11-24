module TL.Big where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Console (log)
import Heterogeneous.Mapping (class Mapping, hmap)
import Heterogeneous.Folding (class Folding, hfoldl)
import Record.Studio (sequenceRecord, mapRecord)

data WrapJust = WrapJust
instance Mapping WrapJust a (Maybe a) where
  mapping WrapJust = Just

data CountFields = CountFields
instance Folding CountFields Int a Int where
  folding CountFields acc _ = acc + 1

type Big = { f1 :: Int, f2 :: Int, f3 :: String, f4 :: Int, f5 :: Int, f6 :: String, f7 :: Int, f8 :: Int, f9 :: String, f10 :: Int, f11 :: Int, f12 :: String, f13 :: Int, f14 :: Int, f15 :: String, f16 :: Int, f17 :: Int, f18 :: String, f19 :: Int, f20 :: Int, f21 :: String, f22 :: Int, f23 :: Int, f24 :: String, f25 :: Int, f26 :: Int, f27 :: String, f28 :: Int, f29 :: Int, f30 :: String, f31 :: Int, f32 :: Int, f33 :: String, f34 :: Int, f35 :: Int, f36 :: String, f37 :: Int, f38 :: Int, f39 :: String, f40 :: Int, f41 :: Int, f42 :: String, f43 :: Int, f44 :: Int, f45 :: String, f46 :: Int, f47 :: Int, f48 :: String, f49 :: Int, f50 :: Int, f51 :: String, f52 :: Int, f53 :: Int, f54 :: String, f55 :: Int, f56 :: Int, f57 :: String, f58 :: Int, f59 :: Int, f60 :: String }

big :: Big
big = { f1: 1, f2: 2, f3: "s3", f4: 4, f5: 5, f6: "s6", f7: 7, f8: 8, f9: "s9", f10: 10, f11: 11, f12: "s12", f13: 13, f14: 14, f15: "s15", f16: 16, f17: 17, f18: "s18", f19: 19, f20: 20, f21: "s21", f22: 22, f23: 23, f24: "s24", f25: 25, f26: 26, f27: "s27", f28: 28, f29: 29, f30: "s30", f31: 31, f32: 32, f33: "s33", f34: 34, f35: 35, f36: "s36", f37: 37, f38: 38, f39: "s39", f40: 40, f41: 41, f42: "s42", f43: 43, f44: 44, f45: "s45", f46: 46, f47: 47, f48: "s48", f49: 49, f50: 50, f51: "s51", f52: 52, f53: 53, f54: "s54", f55: 55, f56: 56, f57: "s57", f58: 58, f59: 59, f60: "s60" }

main :: Effect Unit
main = do
  log (show big)
  log (show (hmap WrapJust big))
  log (show (hfoldl CountFields 0 big))
  log (show (sequenceRecord (hmap WrapJust big) :: Maybe Big))
  log (show (big == big { f1 = 2 }))
  log (show (compare big big { f59 = 0 }))
