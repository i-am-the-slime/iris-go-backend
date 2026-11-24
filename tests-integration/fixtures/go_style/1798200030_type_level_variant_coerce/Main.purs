module TL.VCoerce where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, unwrap, wrap)
import Data.Variant (Variant, inj, match, on, default, prj, expand)
import Effect (Effect)
import Effect.Console (log)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

unsafeExpandVariant :: forall a b. Variant a -> Variant b
unsafeExpandVariant = unsafeCoerce

type Small = (a :: Int)
type Big = (a :: Int, b :: String, c :: Array Int)

showBig :: Variant Big -> String
showBig = match { a: \n -> "a" <> show n, b: \s -> "b" <> s, c: \xs -> "c" <> show xs }

newtype Event = Event (Variant (click :: { x :: Int, y :: Int }, key :: String))

derive instance Newtype Event _

describeEvent :: Event -> String
describeEvent (Event v) = v # match
  { click: \{ x, y } -> "click " <> show x <> "," <> show y
  , key: \k -> "key " <> k
  }

polyInj :: forall a. a -> Variant (x :: a, y :: Unit)
polyInj = inj (Proxy @"x")

type Handlers = { a :: Int -> String, b :: String -> String, c :: Array Int -> String }

handlersAsSmaller :: Handlers -> { a :: Int -> String }
handlersAsSmaller = unsafeCoerce

main :: Effect Unit
main = do
  let small = inj (Proxy @"a") 1 :: Variant Small
  log (showBig (unsafeExpandVariant small))
  let smalls = [ small, inj (Proxy @"a") 2 ]
  log (show (smalls <#> unsafeExpandVariant <#> showBig))
  let bigs = unsafeCoerce smalls :: Array (Variant Big)
  log (show (bigs <#> showBig))
  log (show bigs)
  let record = { payload: small, n: 3 }
  let recordBig = unsafeCoerce record :: { payload :: Variant Big, n :: Int }
  log (showBig recordBig.payload)
  log (describeEvent (wrap (inj (Proxy @"click") { x: 1, y: 2 })))
  log (describeEvent (unsafeCoerce (inj (Proxy @"key") "k" :: Variant (key :: String))))
  log (show (prj (Proxy @"x") (polyInj [ 1 ]) :: Maybe (Array Int)))
  log (show (polyInj "s"))
  log (show (polyInj (Just 1.5)))
  let maybeV = Just small
  log (show ((unsafeCoerce maybeV :: Maybe (Variant Big)) <#> showBig))
  let fnV = (\n -> inj (Proxy @"a") n) :: Int -> Variant Small
  log (showBig ((unsafeCoerce fnV :: Int -> Variant Big) 5))
  log ((handlersAsSmaller { a: show, b: identity, c: show }).a 9)
  let backToSmall = unsafeCoerce (inj (Proxy @"a") 7 :: Variant Big) :: Variant Small
  log (show backToSmall)
  log (show (backToSmall == small))
  log (show (Array.nub [ small, small, inj (Proxy @"a") 9 ]))
