module Main where

import Prelude

import Data.Array (index, length, snoc)
import Data.Maybe (Maybe(..), fromMaybe)
import Effect (Effect)
import Effect.Ref as Ref

type Tally = { count :: Int, label :: String }

walk :: Array Int -> Array String
walk commands = step commands 0 1 2 3 4 "s" "t" "u" Nothing Nothing [] [] { count: 0, label: "start" } 10 20 30 "p" "q" false 0 7 8

walkShifted :: Array Int -> Array String
walkShifted commands = step commands 0 5 2 3 (length commands) "s" "t" "v" (Just 1) Nothing [ 9 ] [] { count: 1, label: "shifted" } 10 20 30 "p" "q" true 0 7 8

step
  :: Array Int
  -> Int
  -> Int
  -> Int
  -> Int
  -> Int
  -> String
  -> String
  -> String
  -> Maybe Int
  -> Maybe Int
  -> Array Int
  -> Array Int
  -> Tally
  -> Int
  -> Int
  -> Int
  -> String
  -> String
  -> Boolean
  -> Int
  -> Int
  -> Int
  -> Array String
step commands i a b c d s t u m n xs ys r e f g p q flag k h w
  | i >= length commands =
      [ show [ a, b, c, d, e, f, g, k, h, w ]
      , s <> "|" <> t <> "|" <> u <> "|" <> p <> "|" <> q
      , show [ m, n ]
      , show xs <> show ys
      , show r.count <> r.label
      , show flag
      ]
  | otherwise = case fromMaybe 0 (index commands i) `mod` 12 of
      0 -> step commands (i + 1) b a c d s t u m n xs ys r e f g p q flag k h w
      1 -> step commands (i + 1) a b c d (s <> t) s u m n xs ys r e f g p q flag k h w
      2 -> step commands (i + 1) a b c d s t u (Just (a + b)) m xs ys r e f g p q flag k h w
      3 -> step commands (i + 1) a b c d s t u m n (snoc xs c) xs r e f g p q flag k h w
      4 -> step commands (i + 1) a b c d s t u m n xs ys { count: r.count + 1, label: r.label <> u } e f g p q flag k h w
      5 -> step commands (i + 1) a b c d s t u m n xs ys r f g e p q flag k h w
      6 -> step commands (i + 1) a b c d s t u m n xs ys r e f g q p (not flag) k h w
      7 -> step commands (i + 1) a b (c + d) c s t u m n xs ys r e f g p q flag k h w
      8 -> step commands (i + 1) a b c d s t (u <> p) m n xs ys r e f g p q flag (k + fromMaybe 0 n) h w
      9 -> step commands (i + 1) a b c d s t u n m xs ys r e f g p q flag k w h
      10 -> step commands (i + 1) a b c d s t u m n ys xs r e f g p q flag k h (w + h)
      _ -> step commands (i + 1) a b c d s t u m n xs ys r e f g p q flag (k + 1) h w

main :: Effect (Array String)
main = do
  commands <- Ref.new [ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 2, 9, 8, 3, 3, 10, 1, 0, 7, 7, 5, 6, 4, 11, 2, 8 ]
  current <- Ref.read commands
  pure (walk current <> walkShifted current)
