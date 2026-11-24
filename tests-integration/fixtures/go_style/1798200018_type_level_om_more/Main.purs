module TL.OmMore where

import Prelude

import Control.Alt ((<|>))
import Control.Monad.Reader.Class (asks)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Aff, launchAff_)
import Effect.Aff as Aff
import Effect.Aff.Class (liftAff)
import Effect.Class.Console (log)
import Yoga.Om (Om, fatal, noteM, orFail, runOm, runOms, throw, throwLeftAs, throwUnless, throwWhen, unliftAff, unliftAffFn, widenCtx, runReader, launchOm_)
import Yoga.Om.Ref as OmRef
import Data.Variant (inj)
import Type.Proxy (Proxy(..))

type Ctx = { base :: Int }

validate :: Int -> Om Ctx (negative :: Int, tooLarge :: Int) Int
validate n = do
  throwWhen { negative: n } (n < 0)
  throwUnless { tooLarge: n } (n < 100)
  base <- asks _.base
  pure (base + n)

parseNumber :: String -> Either String Int
parseNumber = case _ of
  "one" -> Right 1
  "two" -> Right 2
  other -> Left other

parsed :: String -> Om Ctx (unparseable :: String) Int
parsed s = parseNumber s # throwLeftAs (inj (Proxy @"unparseable"))

firstSuccessful :: Om Ctx () Int
firstSuccessful = fatal "first" <|> fatal "second" <|> pure 3

counter :: Om Ctx () Int
counter = do
  ref <- OmRef.new 0
  OmRef.modify_ (_ + 5) ref
  OmRef.modify_ (_ * 2) ref
  OmRef.read ref

unlifted :: Om Ctx () String
unlifted = do
  aff <- unliftAff (validate 5)
  result <- Aff.attempt aff # liftAff
  pure case result of
    Right (Right n) -> "unlifted ok " <> show n
    Right (Left _) -> "unlifted om error"
    Left _ -> "unlifted aff error"

unliftedFn :: Om Ctx () (Int -> Aff Int)
unliftedFn = unliftAffFn \n -> asks _.base <#> (_ * n)

handlers :: forall a. Show a => (a -> String) -> { exception :: Aff.Error -> Aff String, negative :: Int -> Aff String, tooLarge :: Int -> Aff String }
handlers _ =
  { exception: \e -> pure ("exception " <> Aff.message e)
  , negative: \n -> pure ("negative " <> show n)
  , tooLarge: \n -> pure ("tooLarge " <> show n)
  }

main :: Effect Unit
main = launchAff_ do
  let run om = runOm { base: 10 } (handlers (show :: Int -> String)) (om <#> show)
  run (validate 5) >>= log
  runOm { base: 10 } { exception: \_ -> pure "exc" } unlifted >>= log
  run (validate (-1)) >>= log
  run (validate 500) >>= log
  r1 <- runOm { base: 0 } { exception: \_ -> pure "exc", unparseable: \s -> pure ("cannot parse " <> s) } (parsed "two" <#> show)
  log r1
  r2 <- runOm { base: 0 } { exception: \_ -> pure "exc", unparseable: \s -> pure ("cannot parse " <> s) } (parsed "three" <#> show)
  log r2
  r3 <- runOm { base: 0 } { exception: \e -> pure (-1) } firstSuccessful
  log (show r3)
  r4 <- runOm { base: 0 } { exception: \e -> pure (-1) } counter
  log (show r4)
  f <- runOm { base: 7 } { exception: \_ -> pure (const (pure 0)) } unliftedFn
  six <- f 6
  log (show six)
  r5 <- runOm { base: 1 } { exception: \_ -> pure 0 } (orFail (pure 99) Nothing)
  log (show r5)
  r6 <- runOm { base: 1 } { exception: \_ -> pure 0 } (noteM (pure (inj (Proxy @"exception") (Aff.error "noted"))) (Just 4))
  log (show r6)
  let fired = runOms { base: 3 } { exception: \e -> log ("runOms exc " <> Aff.message e) } { one: (asks _.base >>= \b -> log ("one " <> show b) :: Om Ctx () Unit), two: (fatal "two failed" :: Om Ctx () Unit) }
  fired.one
  fired.two
