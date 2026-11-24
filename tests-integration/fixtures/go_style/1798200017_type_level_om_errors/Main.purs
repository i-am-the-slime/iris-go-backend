module TL.OmErrors where

import Prelude

import Control.Monad.Error.Class (throwError)
import Control.Monad.Reader.Class (ask, asks)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Variant (Variant, inj)
import Effect (Effect)
import Effect.Aff (Aff, launchAff_, message)
import Effect.Class (liftEffect)
import Effect.Class.Console (log)
import Type.Proxy (Proxy(..))
import Type.Row (type (+))
import Yoga.Om (Om, expandErr, handleErrors, handleErrors', launchOm, mapError, note, onError, runOm, runReader, throw, fatal, widenCtx, tap)
import Yoga.Om as Om

type Ctx = { userName :: String, limit :: Int }

type NotFound r = (notFound :: String | r)
type TooBig r = (tooBig :: Int | r)

findUser :: forall err. Int -> Om Ctx (NotFound err) String
findUser userId = do
  name <- asks _.userName
  when (userId /= 1) do
    throw { notFound: "user " <> show userId }
  pure name

checkLimit :: forall err. Int -> Om Ctx (TooBig err) Int
checkLimit n = do
  limit <- asks _.limit
  when (n > limit) do
    throw { tooBig: n }
  pure n

combined :: Int -> Int -> Om Ctx (NotFound + TooBig ()) String
combined userId amount = do
  name <- findUser userId
  checked <- checkLimit amount
  ctx <- ask
  pure (name <> " spends " <> show checked <> " of " <> show ctx.limit)

recovered :: Int -> Int -> Om Ctx () String
recovered userId amount = combined userId amount # handleErrors
  { notFound: \who -> pure ("recovered notFound " <> who)
  , tooBig: \n -> pure ("recovered tooBig " <> show n)
  }

viaOnError :: Int -> Om Ctx (TooBig ()) String
viaOnError userId = combined userId 1 # onError @"notFound" (\who -> pure ("onError " <> who))

viaMapError :: Int -> Om Ctx (NotFound + (tooLarge :: String)) String
viaMapError amount = combined 1 amount # mapError @"tooBig" @"tooLarge" (\n -> "too large: " <> show n)

viaHandleErrors' :: Int -> Om Ctx () String
viaHandleErrors' userId = combined userId 1 # handleErrors' \_ -> pure "handled generically"

onlyNotFound :: Om Ctx (NotFound ()) String
onlyNotFound = findUser 2

widened :: Om Ctx (NotFound + TooBig + (other :: Unit)) String
widened = expandErr onlyNotFound

noteMissing :: Maybe Int -> Om Ctx (missing :: Unit) Int
noteMissing = note { missing: unit }

runWith :: forall err a. Show a => String -> Om Ctx err a -> Aff Unit
runWith label om = do
  result <- runReader { userName: "ann", limit: 10 } om
  log (label <> ": " <> showResult result)
  where
  showResult = case _ of
    Left _ -> "Left <error>"
    Right a -> "Right " <> show a

runShowing :: String -> Om Ctx (NotFound + TooBig ()) String -> Aff Unit
runShowing label om = do
  text <- runOm { userName: "ann", limit: 10 } handlers om
  log (label <> ": " <> text)
  where
  handlers =
    { exception: \e -> pure ("exception " <> message e)
    , notFound: \who -> pure ("notFound " <> who)
    , tooBig: \n -> pure ("tooBig " <> show n)
    }

main :: Effect Unit
main = launchAff_ do
  runShowing "ok" (combined 1 5)
  runShowing "nf" (combined 2 5)
  runShowing "big" (combined 1 50)
  runShowing "fatal" (fatal "boom")
  runShowing "thrownVariant" (throwError (inj (Proxy @"tooBig") 99))
  runWith "recovered nf" (recovered 3 1)
  runWith "recovered big" (recovered 1 11)
  runWith "recovered ok" (recovered 1 1)
  runWith "onError" (viaOnError 5)
  runWith "onError ok" (viaOnError 1)
  runWith "mapError" (viaMapError 100)
  runWith "mapError ok" (viaMapError 2)
  runWith "handleErrors'" (viaHandleErrors' 9)
  runWith "widened" widened
  runWith "note" (noteMissing Nothing)
  runWith "note ok" (noteMissing (Just 3))
  runWith "liftEffect" (liftEffect (pure 7) :: Om Ctx () Int)
  runWith "tap" (tap (\n -> log ("tapped " <> show n)) 5 :: Om Ctx () Int)
  mapped <- runOm { userName: "z", limit: 0 } { exception: \_ -> pure "x", tooLarge: \s -> pure s, notFound: \s -> pure s } (viaMapError 3)
  log mapped
  pure unit
