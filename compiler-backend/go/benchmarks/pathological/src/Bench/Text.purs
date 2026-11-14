-- | Sample text for the string benchmarks: the same sentence shapes in ASCII and in text whose
-- | characters take one, two and four UTF-8 bytes and one or two UTF-16 code units.
module Bench.Text
  ( ascii
  , unicode
  ) where

import Prelude

import Data.Array ((..))
import Data.Array as Array
import Data.Maybe (fromMaybe)
import Data.String (joinWith)

ascii :: Int -> String
ascii words = joinWith " " (map asciiWord (0 .. (words - 1)))
  where
  asciiWord i = asciiVocabulary `at` i

unicode :: Int -> String
unicode words = joinWith " " (map unicodeWord (0 .. (words - 1)))
  where
  unicodeWord i = unicodeVocabulary `at` i

at :: Array String -> Int -> String
at vocabulary i = fromMaybe "" (Array.index vocabulary (i `mod` Array.length vocabulary))

asciiVocabulary :: Array String
asciiVocabulary =
  [ "the", "quick", "brown", "fox", "jumps", "over", "lazy", "dog", "while", "seven", "wizards"
  , "box", "jovial", "quartz", "sphinx", "of", "black", "judge", "my", "vow", "pack", "liquor"
  ]

unicodeVocabulary :: Array String
unicodeVocabulary =
  [ "東京", "の", "空", "😀", "naïve", "café", "🦊", "跳ぶ", "über", "犬", "𝄞music", "日本語"
  , "🎉🎉", "ж", "Ωmega", "spät", "猫", "が", "好き", "👩‍💻", "ok", "ñandú"
  ]
