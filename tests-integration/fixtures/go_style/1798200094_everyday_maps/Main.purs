module Fun.Maps where

import Prelude

import Data.Either (Either(..))
import Data.Functor.Compose (Compose(..))
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, un)
import Data.Show.Generic (genericShow)
import Effect (Effect)
import Effect.Console (log)

newtype Boxed a = Boxed { label :: String, value :: Maybe a }

instance Functor Boxed where
  map f (Boxed { label, value }) = Boxed { label, value: value <#> f }

newtype Pair a = Pair (Array a)

instance Functor Pair where
  map f (Pair items) = Pair (f <$> items)

newtype Wrapped a = Wrapped (Maybe a)

derive instance Functor Wrapped
derive instance Newtype (Wrapped a) _
derive instance Generic (Wrapped a) _
instance Show a => Show (Wrapped a) where
  show = genericShow

newtype Chained a = Chained (Array a)

instance Functor Chained where
  map f (Chained items) = Chained (items <#> f <#> identity)

showBoxed :: forall a. Show a => Boxed a -> String
showBoxed (Boxed { label, value }) = label <> "=" <> show value

showPair :: forall a. Show a => Pair a -> String
showPair (Pair items) = "Pair" <> show items

showChained :: forall a. Show a => Chained a -> String
showChained (Chained items) = "Chained" <> show items

main :: Effect Unit
main = do
  let numbers = [ 1, 2, 3 ]
  log "-- array"
  log $ show (map (_ + 1) numbers)
  log $ show ((_ + 1) <$> numbers)
  log $ show (numbers <#> (_ + 1))
  log $ show (numbers # map (_ + 1))
  log $ show (numbers <#> (_ + 1) <#> (_ * 2) <#> show <#> (_ <> "!") <#> (\s -> s <> s))
  log $ show (map (\s -> s <> s) $ map (_ <> "!") $ map show $ map (_ * 2) $ map (_ + 1) numbers)
  log $ show ((\s -> s <> s) <$> ((_ <> "!") <$> (show <$> ((_ * 2) <$> ((_ + 1) <$> numbers)))))
  log $ show (numbers # map (_ + 1) # map (_ * 2) # map show # map (_ <> "!") # map (\s -> s <> s))
  log $ show (map (\s -> s <> s) (numbers <#> (_ + 1) # map (_ * 2) <#> show) <#> (_ <> "?"))
  log "-- maybe"
  log $ show (Just 3 <#> (_ + 1) <#> (_ * 2) <#> show)
  log $ show (show <$> ((_ * 2) <$> ((_ + 1) <$> Just 3)))
  log $ show (Nothing <#> (_ + 1) <#> (_ * 2) <#> show :: Maybe String)
  log $ show (Just 3 # map (_ + 1) # map (_ * 2) # map show)
  log "-- either"
  log $ show ((Right 3 :: Either String Int) <#> (_ + 1) <#> (_ * 2) <#> show)
  log $ show ((Left "nope" :: Either String Int) <#> (_ + 1) <#> (_ * 2) <#> show)
  log $ show (map show (map (_ * 2) (map (_ + 1) (Right 3 :: Either String Int))))
  log "-- newtype functors"
  let boxed = Boxed { label: "box", value: Just 10 }
  log $ showBoxed (boxed <#> (_ + 1) <#> (_ * 2) <#> show <#> (_ <> "!"))
  log $ showBoxed (map (_ <> "!") (map show (map (_ * 2) (map (_ + 1) boxed))))
  log $ showBoxed (boxed # map (_ + 1) # map (_ * 2))
  log $ showPair (Pair numbers <#> (_ + 1) <#> (_ * 2) <#> show)
  log $ showPair (show <$> ((_ * 2) <$> ((_ + 1) <$> Pair numbers)))
  log $ show (Wrapped (Just 5) <#> (_ + 1) <#> (_ * 2) <#> show)
  log $ show (un Wrapped (Wrapped (Just 5) <#> (_ + 1)))
  log $ showChained (Chained numbers <#> (_ + 1) <#> (_ * 2) <#> show <#> (_ <> "."))
  log "-- functor of functor"
  let nested = [ Just 1, Nothing, Just 3 ]
  log $ show (nested <#> map (_ + 1) <#> map (_ * 2))
  log $ show (map (map show) (map (map (_ + 1)) nested))
  log $ show (nested # map (_ <#> (_ + 1)) # map (_ <#> show))
  let composed = Compose nested
  log $ show (composed <#> (_ + 1) <#> (_ * 10) <#> show)
  log $ show (map show (map (_ + 1) composed))
  log "-- <@> $> <$ void"
  log $ show ([ (_ + 1), (_ * 2), (_ - 3) ] <@> 10)
  log $ show (map (_ $ 10) [ (_ + 1), (_ * 2), (_ - 3) ])
  log $ show (Just 1 $> "x")
  log $ show ("y" <$ Just 1)
  log $ show (numbers $> "z")
  log $ show (void numbers)
  log $ show (void (Just 9))
  log $ show (void (Nothing :: Maybe Int))
  effectful <- pure 4 <#> (_ + 1) <#> (_ * 3) <#> show
  log effectful
  effectful2 <- map show (map (_ * 3) (map (_ + 1) (pure 4)))
  log effectful2
  effectful3 <- (pure 4 :: Effect Int) # map (_ + 1) # map (_ * 3)
  log $ show effectful3
  unit3 <- void (pure 3 :: Effect Int)
  log $ show unit3
  str <- "s" <$ log "side"
  log str
