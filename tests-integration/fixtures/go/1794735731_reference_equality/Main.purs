module Main where

import Prelude

import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Unsafe (unsafePerformEffect)
import Effect.Ref as Ref
import Unsafe.Reference (unsafeRefEq)

data Room = Kitchen | Garden

data Shape = Circle Number | Square Number

data Chain = End | Link Int Chain

type Handler = { name :: String, run :: Int -> Int }

adder :: Int -> Int -> Int
adder step n = n + step

same :: forall a. a -> a -> Boolean
same = unsafeRefEq

int :: Int -> Int -> Boolean
int = same

number :: Number -> Number -> Boolean
number = same

boolean :: Boolean -> Boolean -> Boolean
boolean = same

char :: Char -> Char -> Boolean
char = same

string :: String -> String -> Boolean
string = same

unit' :: Unit -> Unit -> Boolean
unit' = same

enumeration :: Room -> Room -> Boolean
enumeration = same

function :: (Int -> Int) -> (Int -> Int) -> Boolean
function = same

effect :: Effect Unit -> Effect Unit -> Boolean
effect = same

array :: Array Int -> Array Int -> Boolean
array = same

reference :: Ref Int -> Ref Int -> Boolean
reference = same

record :: { x :: Int, y :: Number } -> { x :: Int, y :: Number } -> Boolean
record = same

recordWithFunction :: Handler -> Handler -> Boolean
recordWithFunction = same

unboxed :: Shape -> Shape -> Boolean
unboxed = same

boxed :: Chain -> Chain -> Boolean
boxed = same

counter :: Ref Int
counter = unsafePerformEffect (Ref.new 0)

main :: Array Boolean
main =
  [ int 1 2
  , number 1.0 1.0
  , boolean true false
  , char 'a' 'a'
  , string "a" "b"
  , unit' unit unit
  , enumeration Kitchen Garden
  , function (adder 1) (adder 2)
  , effect (pure unit) (pure unit)
  , array [ 1 ] [ 1 ]
  , reference counter counter
  , record { x: 1, y: 2.0 } { x: 1, y: 3.0 }
  , recordWithFunction { name: "a", run: adder 1 } { name: "a", run: adder 2 }
  , unboxed (Circle 1.0) (Square 1.0)
  , boxed (Link 1 End) End
  ]
