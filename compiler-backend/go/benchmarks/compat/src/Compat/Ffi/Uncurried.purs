module Compat.Ffi.Uncurried where

import Prelude

import Data.Array as Array
import Data.Function.Uncurried (Fn2, Fn3, Fn4, Fn10, mkFn2, mkFn3, mkFn4, mkFn10, runFn2, runFn3, runFn4, runFn10)
import Data.Maybe (Maybe(..), fromJust)
import Effect (Effect)
import Effect.Console (log)
import Effect.Ref as Ref
import Effect.Uncurried (EffectFn1, EffectFn2, EffectFn3, mkEffectFn1, mkEffectFn2, mkEffectFn3, runEffectFn1, runEffectFn2, runEffectFn3)
import Partial.Unsafe (unsafePartial, unsafeCrashWith)

add3 :: Fn3 Int Int Int Int
add3 = mkFn3 \a b c -> a + b + c

joinAll :: Fn10 String String String String String String String String String String String
joinAll = mkFn10 \a b c d e f g h i j -> a <> b <> c <> d <> e <> f <> g <> h <> i <> j

weighted :: Fn4 Number Number Number Number Number
weighted = mkFn4 \a b c d -> a * 1.0 + b * 2.0 + c * 3.0 + d * 4.0

pairUp :: forall a b. Fn2 a b { first :: a, second :: b }
pairUp = mkFn2 \first second -> { first, second }

logBoth :: EffectFn2 String Int Unit
logBoth = mkEffectFn2 \label n -> log (label <> "=" <> show n)

accumulate :: EffectFn3 (Ref.Ref Int) Int Int Int
accumulate = mkEffectFn3 \ref a b -> do
  Ref.modify_ (_ + a * b) ref
  Ref.read ref

callTwice :: EffectFn1 (EffectFn1 Int Unit) Unit
callTwice = mkEffectFn1 \callback -> do
  runEffectFn1 callback 1
  runEffectFn1 callback 2

head' :: forall a. Partial => Array a -> a
head' xs = case Array.head xs of
  Just x -> x

classify :: Partial => Int -> String
classify 0 = "zero"
classify 1 = "one"

main :: Effect Unit
main = do
  log (show (runFn3 add3 1 2 3))
  log (runFn10 joinAll "a" "b" "c" "d" "e" "f" "g" "h" "i" "j")
  log (show (runFn4 weighted 1.0 1.0 1.0 1.0))
  log (show (runFn2 pairUp "x" 3))
  runEffectFn2 logBoth "count" 4
  ref <- Ref.new 1
  total <- runEffectFn3 accumulate ref 3 4
  log (show total)
  runEffectFn1 callTwice (mkEffectFn1 \n -> log ("callback " <> show n))
  log (show (unsafePartial (head' [ 5, 6 ])))
  log (unsafePartial (classify 1))
  log (show (unsafePartial (fromJust (Just "just"))))
  log (show (map (runFn2 (mkFn2 (+))) [ 1 ] <*> [ 10, 20 ]))
  when false (unsafeCrashWith "unreachable")
