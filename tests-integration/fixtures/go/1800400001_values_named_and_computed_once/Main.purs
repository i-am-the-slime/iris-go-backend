module Main where

import Prelude

import Data.Array as Array
import Data.Foldable (for_)
import Data.Newtype (class Newtype, un)
import Data.String as String
import Effect (Effect)
import Journal (log)
import Effect.Ref as Ref

newtype Path = Path String

derive instance Newtype Path _

newtype Counter = Counter (Ref.Ref Int)

-- | The method is the literal `"POST"`.
method :: String
method = String.toUpper "post"

-- | The concatenation leaves out the empty arrays: the one array left is the result.
errorsOf :: Array String -> Array String
errorsOf found = Array.concat [ mempty, found, mempty ]

-- | Unwrapping each path copies nothing: the paths are the strings.
joined :: Array Path -> String
joined paths = String.joinWith "/" (paths <#> un Path)

-- | `const` keeps the left element without a call.
lefts :: Array String -> Array Int -> Array String
lefts = Array.zipWith const

-- | One test of `n < 1` chooses both slices.
dropBoth :: Int -> Array Int -> Array String -> { ints :: Array Int, strings :: Array String }
dropBoth n ints strings =
  { ints: if n < 1 then ints else Array.drop n ints
  , strings: if n < 1 then strings else Array.drop n strings
  }

-- | `String.toUpper name` is computed once, before the first log, and both logs read it.
greet :: String -> Effect Unit
greet name = do
  log (String.toUpper name)
  log (String.toUpper name <> "!")

-- | Callers append the padding to what they build, and the string version of `padded` goes.
padded :: Int -> String -> String
padded width text = String.joinWith "" (Array.replicate (width - String.length text) " ") <> text

main :: Effect Unit
main = do
  counter <- Ref.new 0 <#> Counter
  count counter
  words <- Ref.new [ "usr", "bin" ] >>= Ref.read
  numbers <- Ref.new [ 1, 2 ] >>= Ref.read
  log method
  log (show (errorsOf words))
  log (joined (words <#> Path))
  log (show (lefts words numbers))
  for_ numbers \n -> log (show (dropBoth n numbers words))
  for_ words greet
  for_ words \word -> log (padded 5 word <> "|")
  where
  count (Counter ref) = Ref.modify_ (_ + 1) ref
