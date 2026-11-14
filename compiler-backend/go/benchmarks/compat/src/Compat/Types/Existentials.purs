module Compat.Types.Existentials where

import Prelude

import Data.Exists (Exists, mkExists, runExists)
import Data.Leibniz (type (~), coerce, symm)
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (type (/\), (/\))
import Data.Identity (Identity(..))
import Data.Newtype (unwrap)
import Effect (Effect)
import Effect.Console (log)

data ShowBoxF a = ShowBoxF a (a -> String)

type ShowBox = Exists ShowBoxF

box :: forall a. Show a => a -> ShowBox
box a = mkExists (ShowBoxF a show)

render :: ShowBox -> String
render = runExists \(ShowBoxF a f) -> f a

data StreamF a s = StreamF s (s -> Maybe (a /\ s))

type Stream a = Exists (StreamF a)

countdown :: Int -> Stream Int
countdown n = mkExists (StreamF n \s -> if s <= 0 then Nothing else Just (s /\ (s - 1)))

toArray :: forall a. Stream a -> Array a
toArray = runExists \(StreamF seed next) -> unfoldWith next seed

unfoldWith :: forall a s. (s -> Maybe (a /\ s)) -> s -> Array a
unfoldWith next seed = case next seed of
  Nothing -> []
  Just (a /\ rest) -> [ a ] <> unfoldWith next rest

data Value a
  = IntValue (a ~ Int) Int
  | StringValue (a ~ String) String
  | Pair (Value a) (Value a)

evaluate :: forall a. Value a -> a
evaluate (IntValue proof n) = coerce (symm proof) n
evaluate (StringValue proof s) = coerce (symm proof) s
evaluate (Pair a _) = evaluate a

newtype Distance (unit :: Type) = Distance Number
data Metres
data Feet

metres :: Number -> Distance Metres
metres = Distance

toFeet :: Distance Metres -> Distance Feet
toFeet (Distance m) = Distance (m * 3.28084)

type User f = { name :: f String, age :: f Int }

complete :: User Maybe -> Maybe (User Identity)
complete user = ado
  name <- user.name
  age <- user.age
  in { name: Identity name, age: Identity age }

main :: Effect Unit
main = do
  log (show (map render [ box 1, box "two", box [ 3.0 ], box (Just true) ]))
  log (show (evaluate (IntValue identity 41) + 1))
  log (evaluate (Pair (StringValue identity "left") (StringValue identity "right")))
  log (case toFeet (metres 10.0) of Distance feet -> show feet)
  log (show (map (\u -> unwrap u.name <> " " <> show (unwrap u.age)) (complete { name: Just "Ann", age: Just 30 })))
  log (show (map (\u -> unwrap u.name) (complete { name: Just "Bob", age: Nothing })))
  log (show (toArray (countdown 3)))
