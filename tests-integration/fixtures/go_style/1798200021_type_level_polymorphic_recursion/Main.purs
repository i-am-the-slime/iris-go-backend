module TL.PolyRec where

import Prelude

import Control.Monad.Rec.Class (Step(..), tailRecM)
import Control.Monad.ST as ST
import Control.Monad.ST.Ref as STRef
import Data.Array as Array
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (launchAff_)
import Effect.Class.Console (log)
import Yoga.Om (Om, runOm)

data Nested a = Flat a | Nest (Nested (Array a))

showNested :: forall a. Show a => Nested a -> String
showNested = case _ of
  Flat a -> "Flat " <> show a
  Nest inner -> "Nest (" <> showNested inner <> ")"

depth :: forall a. Nested a -> Int
depth = case _ of
  Flat _ -> 0
  Nest inner -> 1 + depth inner

build :: forall a. Int -> a -> Nested a
build n a = if n <= 0 then Flat a else Nest (build (n - 1) [ a ])

class Container f where
  toArray :: forall a. f a -> Array a

instance Container Maybe where
  toArray = case _ of
    Just a -> [ a ]
    Nothing -> []

instance Container Array where
  toArray = identity

sizeOf :: forall @f a. Container f => f a -> Int
sizeOf = toArray >>> Array.length

countDown :: Int -> Om {} () Int
countDown start = tailRecM step { n: start, acc: 0 }
  where
  step { n, acc } = pure if n == 0 then Done acc else Loop { n: n - 1, acc: acc + n }

sumST :: Int -> Int
sumST n = ST.run do
  ref <- STRef.new { total: 0, count: 0 }
  ST.for 0 n \i -> void (STRef.modify (\r -> r { total = r.total + i, count = r.count + 1 }) ref)
  STRef.read ref <#> \r -> r.total * 1000 + r.count

main :: Effect Unit
main = launchAff_ do
  log (showNested (build 3 1))
  log (showNested (build 2 "s"))
  log (show (depth (build 5 unit)))
  log (show (sizeOf @Maybe (Just 1)))
  log (show (sizeOf @Array [ 1, 2, 3 ]))
  total <- runOm {} { exception: \_ -> pure (-1) } (countDown 100000)
  log (show total)
  log (show (sumST 100))
