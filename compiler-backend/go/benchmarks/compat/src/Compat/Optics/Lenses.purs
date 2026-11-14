module Compat.Optics.Lenses where

import Prelude

import Data.Lens (Lens', Prism', Traversal', Iso', iso, lens, over, preview, prism', review, set, toListOf, traverseOf, traversed, view, (%~), (.~), (^.), (^?))
import Data.Lens.At (at)
import Data.Lens.Index (ix)
import Data.Lens.Record (prop)
import Data.List as List
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested ((/\))
import Data.Newtype (class Newtype)
import Data.Lens.Iso.Newtype (_Newtype)
import Effect (Effect)
import Effect.Console (log)
import Type.Proxy (Proxy(..))

type Address = { street :: String, number :: Int }
type Person = { name :: String, address :: Address, pets :: Array String }

data Shape = Circle Number | Square Number

newtype Celsius = Celsius Number
derive instance Newtype Celsius _

_address :: forall r. Lens' { address :: Address | r } Address
_address = prop (Proxy @"address")

_street :: forall r. Lens' { street :: String | r } String
_street = prop (Proxy @"street")

_number :: Lens' Address Int
_number = lens _.number (_ { number = _ })

_pets :: Traversal' Person String
_pets = prop (Proxy @"pets") <<< traversed

_circle :: Prism' Shape Number
_circle = prism' Circle case _ of
  Circle radius -> Just radius
  _ -> Nothing

_fahrenheit :: Iso' Celsius Number
_fahrenheit = _Newtype <<< iso (\c -> c * 9.0 / 5.0 + 32.0) (\f -> (f - 32.0) * 5.0 / 9.0)

main :: Effect Unit
main = do
  log (view (_address <<< _street) alice)
  log (show (alice ^. _address <<< _number))
  let moved = set (_address <<< _street) "Elm Street" alice
  log moved.address.street
  log (show (over _pets (_ <> "!") alice).pets)
  log (show (toListOf _pets alice))
  log (show ((_address <<< _number) %~ (_ * 10) $ alice).address.number)
  log (show (((_address <<< _street) .~ "Oak" $ alice).address))
  log (show (preview _circle (Circle 2.0)) <> " " <> show (Square 3.0 ^? _circle))
  log (case review _circle 1.5 of
    Circle r -> "circle " <> show r
    Square s -> "square " <> show s)
  log (show (view _fahrenheit (Celsius 100.0)) <> " " <> show (over _fahrenheit (_ + 18.0) (Celsius 0.0) # \(Celsius c) -> c))
  log (show (traverseOf _pets (\pet -> if pet == "" then Nothing else Just (pet <> "?")) alice <#> _.pets))
  log (show (preview (ix 1) [ 10, 20, 30 ]) <> " " <> show (set (ix 5) 0 [ 1, 2 ]))
  let scores = Map.fromFoldable [ "ann" /\ 3, "bob" /\ 5 ]
  log (show (view (at "bob") scores) <> " " <> show (Map.toUnfoldable (set (at "cat") (Just 1) scores) :: List.List _))
  where
  alice = { name: "Alice", address: { street: "Main", number: 7 }, pets: [ "cat", "dog" ] }
