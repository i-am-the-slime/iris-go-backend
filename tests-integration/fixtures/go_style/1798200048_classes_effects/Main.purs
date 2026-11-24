module T.Eff where

import Prelude

import Control.Monad.ST as ST
import Control.Monad.ST.Ref as STRef
import Data.Array as Array
import Data.Array.ST as STArray
import Data.Either (Either(..), either)
import Data.Foldable (for_, traverse_)
import Data.Maybe (Maybe(..))
import Data.String.Regex as Regex
import Data.String.Regex.Flags (global, ignoreCase, noFlags, multiline, unicode)
import Data.Traversable (for)
import Effect (Effect, foreachE, whileE, forE)
import Effect.Console (log)
import Effect.Exception (catchException, error, message, throw, try, throwException)
import Effect.Ref as Ref
import Data.Lazy as Lazy
import Control.Lazy (fix)

sumST :: Array Int -> Int
sumST xs = ST.run do
  total <- STRef.new 0
  ST.foreach xs \x -> void (STRef.modify (_ + x) total)
  STRef.read total

sortedST :: Array Int -> Array Int
sortedST xs = STArray.run do
  arr <- STArray.thaw xs
  _ <- STArray.sort arr
  _ <- STArray.push 999 arr
  pure arr

main :: Effect Unit
main = do
  counter <- Ref.new { hits: 0, log: [] }
  for_ [ "a", "b", "c" ] \name -> Ref.modify_ (\s -> s { hits = s.hits + 1, log = Array.snoc s.log name }) counter
  Ref.read counter >>= show >>> log
  foreachE [ 1, 2 ] (show >>> log)
  forE 0 3 (\i -> log ("forE " <> show i))
  n <- Ref.new 0
  whileE ((_ < 3) <$> Ref.read n) (Ref.modify_ (_ + 1) n)
  Ref.read n >>= show >>> log
  log (show (sumST [ 1, 2, 3 ]) <> show (sortedST [ 3, 1, 2 ]))
  result <- try (throw "boom")
  log (either message (const "no") (result :: Either _ Unit))
  caught <- catchException (\e -> pure ("caught " <> message e)) (throwException (error "bad") *> pure "unreached")
  log caught
  doubled <- for [ 1, 2 ] \i -> pure (i * 2)
  log (show doubled)
  let lazyValue = Lazy.defer \_ -> 6 * 7
  log (show (Lazy.force lazyValue) <> show (Lazy.force (map (_ + 1) lazyValue)))
  let fact = fix \self k -> if k <= 1 then 1 else k * self (k - 1)
  log (show (fact 10))
  -- regex: features JS supports
  let tryRegex pattern flags input = case Regex.regex pattern flags of
        Left err -> "ERR"
        Right re -> show (Regex.match re input) <> " " <> Regex.replace re "<$&>" input <> " " <> show (Regex.split re input) <> " " <> show (Regex.test re input)
  log (tryRegex "\\d+" global "a1b22c333")
  log (tryRegex "(\\w+)@(\\w+)" noFlags "x foo@bar y")
  log (tryRegex "^b" (global <> multiline) "a\nb\nbb")
  log (tryRegex "HELLO" ignoreCase "hello Hello")
  log (tryRegex "a(?=b)" global "ab ac ab")
  log (tryRegex "(a)\\1" global "aa ab")
  log (tryRegex "." (global <> unicode) "😀x")
  log (tryRegex "(?<year>\\d{4})" noFlags "in 2024")
  log (tryRegex "[" noFlags "x")
  log (tryRegex "\\bcat\\b" global "cat concat cat.")
  log (tryRegex "x*" global "axxb")
