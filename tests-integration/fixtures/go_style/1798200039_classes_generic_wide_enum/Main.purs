module T.Big where

import Prelude

import Data.Array as Array
import Data.Bounded.Generic (genericBottom, genericTop)
import Data.Enum (class BoundedEnum, class Enum, enumFromTo)
import Data.Enum.Generic (genericCardinality, genericFromEnum, genericPred, genericSucc, genericToEnum)
import Data.Eq.Generic (genericEq)
import Data.Generic.Rep (class Generic)
import Data.Ord.Generic (genericCompare)
import Data.Show.Generic (genericShow)
import Effect (Effect)
import Effect.Console (log)

data Op = C00 | C01 | C02 | C03 | C04 | C05 | C06 | C07 | C08 | C09 | C10 | C11 | C12 | C13 | C14 | C15 | C16 | C17 | C18 | C19 | C20 | C21 | C22 | C23 | C24 | C25 | C26 | C27 | C28 | C29 | C30 | C31 | C32 | C33 | C34 | C35 | C36 | C37 | C38 | C39
derive instance Generic Op _
instance Show Op where show = genericShow
instance Eq Op where eq = genericEq
instance Ord Op where compare = genericCompare
instance Bounded Op where
  bottom = genericBottom
  top = genericTop
instance Enum Op where
  succ = genericSucc
  pred = genericPred
instance BoundedEnum Op where
  cardinality = genericCardinality
  toEnum = genericToEnum
  fromEnum = genericFromEnum

data Payload = P00 Int String | P01 Int String | P02 Int String | P03 Int String | P04 Int String | P05 Int String | P06 Int String | P07 Int String | P08 Int String | P09 Int String | P10 Int String | P11 Int String | P12 Int String | P13 Int String | P14 Int String | P15 Int String | P16 Int String | P17 Int String | P18 Int String | P19 Int String | P20 Int String | P21 Int String | P22 Int String | P23 Int String | P24 Int String | P25 Int String | P26 Int String | P27 Int String | P28 Int String | P29 Int String | P30 Int String | P31 Int String | P32 Int String | P33 Int String | P34 Int String | P35 Int String | P36 Int String | P37 Int String | P38 Int String | P39 Int String
derive instance Generic Payload _
instance Show Payload where show = genericShow
derive instance Eq Payload
derive instance Ord Payload

type Wide = { field00 :: Int, field01 :: Int, field02 :: Int, field03 :: Int, field04 :: Int, field05 :: Int, field06 :: Int, field07 :: Int, field08 :: Int, field09 :: Int, field10 :: Int, field11 :: Int, field12 :: Int, field13 :: Int, field14 :: Int, field15 :: Int, field16 :: Int, field17 :: Int, field18 :: Int, field19 :: Int, field20 :: Int, field21 :: Int, field22 :: Int, field23 :: Int, field24 :: Int, field25 :: Int, field26 :: Int, field27 :: Int, field28 :: Int, field29 :: Int, field30 :: Int, field31 :: Int, field32 :: Int, field33 :: Int, field34 :: Int, field35 :: Int, field36 :: Int, field37 :: Int, field38 :: Int, field39 :: Int, field40 :: Int, field41 :: Int, field42 :: Int, field43 :: Int, field44 :: Int, field45 :: Int, field46 :: Int, field47 :: Int, field48 :: Int, field49 :: Int, field50 :: Int, field51 :: Int, field52 :: Int, field53 :: Int, field54 :: Int, field55 :: Int, field56 :: Int, field57 :: Int, field58 :: Int, field59 :: Int }

wide :: Wide
wide = { field00: 0, field01: 1, field02: 2, field03: 3, field04: 4, field05: 5, field06: 6, field07: 7, field08: 8, field09: 9, field10: 10, field11: 11, field12: 12, field13: 13, field14: 14, field15: 15, field16: 16, field17: 17, field18: 18, field19: 19, field20: 20, field21: 21, field22: 22, field23: 23, field24: 24, field25: 25, field26: 26, field27: 27, field28: 28, field29: 29, field30: 30, field31: 31, field32: 32, field33: 33, field34: 34, field35: 35, field36: 36, field37: 37, field38: 38, field39: 39, field40: 40, field41: 41, field42: 42, field43: 43, field44: 44, field45: 45, field46: 46, field47: 47, field48: 48, field49: 49, field50: 50, field51: 51, field52: 52, field53: 53, field54: 54, field55: 55, field56: 56, field57: 57, field58: 58, field59: 59 }

main :: Effect Unit
main = do
  let ops = enumFromTo bottom top :: Array Op
  log (show (Array.length ops) <> show (Array.take 3 ops) <> show (Array.last ops))
  log (show (Array.sort (Array.reverse ops) == ops))
  let payloads = [ P39 1 "z", P00 2 "a", P20 0 "m", P20 0 "a" ]
  log (show (Array.sort payloads))
  log (show (wide { field30 = -1, field59 = 99 }))
  log (show (wide == wide) <> show (compare wide (wide { field59 = 0 })))
