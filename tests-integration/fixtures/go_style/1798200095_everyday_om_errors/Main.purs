module Fun.OmErrors where

import Prelude

import Control.Monad.Reader (asks)
import Data.Array ((..))
import Data.Maybe (Maybe(..))
import Data.Traversable (for, traverse)
import Effect (Effect)
import Effect.Aff (Aff, launchAff_, message)
import Effect.Class (liftEffect)
import Effect.Console (log)
import Yoga.Om (Om)
import Yoga.Om as Om

type Config = { limit :: Int, name :: String }

lookupUser :: Int -> Om { limit :: Int } (userMissing :: Int) String
lookupUser id
  | id > 3 = Om.throw { userMissing: id }
  | otherwise = pure ("user" <> show id)

checkLimit :: Int -> Om { limit :: Int } (overLimit :: { value :: Int, limit :: Int }) Int
checkLimit value = do
  limit <- asks _.limit
  Om.throwWhen { overLimit: { value, limit } } (value > limit)
  pure value

combined :: Int -> Om Config (userMissing :: Int, overLimit :: { value :: Int, limit :: Int }) String
combined id = do
  checked <- checkLimit id # Om.expand
  user <- lookupUser checked # Om.expand
  name <- asks _.name
  pure (name <> ":" <> user)

recovered :: Int -> Om Config (overLimit :: { value :: Int, limit :: Int }) String
recovered id = combined id # Om.handleErrors { userMissing: \missing -> pure ("missing " <> show missing) }

mapped :: Int -> Om Config (tooBig :: String, userMissing :: Int) String
mapped id = combined id # Om.mapError @"overLimit" @"tooBig" \{ value } -> "value " <> show value

noted :: Maybe Int -> Om Config (empty :: Unit) Int
noted maybeValue = Om.note { empty: unit } maybeValue <#> (_ * 2)

runAll :: forall a. Show a => Om Config (userMissing :: Int, overLimit :: { value :: Int, limit :: Int }, tooBig :: String, empty :: Unit) a -> Aff String
runAll program = program <#> show # Om.runOm { limit: 5, name: "cfg" }
  { exception: \e -> pure ("exception " <> message e)
  , userMissing: \id -> pure ("userMissing " <> show id)
  , overLimit: \{ value, limit } -> pure ("overLimit " <> show value <> ">" <> show limit)
  , tooBig: \text -> pure ("tooBig " <> text)
  , empty: \_ -> pure "empty"
  }

main :: Effect Unit
main = launchAff_ do
  first <- for (1 .. 6) \id -> runAll (combined id # Om.expand)
  log (show first) # liftEffect
  second <- traverse (recovered >>> Om.expand >>> runAll) (1 .. 6)
  log (show second) # liftEffect
  third <- traverse (\id -> mapped id # Om.expand # runAll) (1 .. 6)
  log (show third) # liftEffect
  fourth <- traverse (noted >>> Om.expand >>> runAll) [ Just 4, Nothing ]
  log (show fourth) # liftEffect
  fifth <- runAll (Om.expandErr (Om.tap (\_ -> liftEffect (log "tapped")) 9 :: Om Config () Int))
  log fifth # liftEffect
  sixth <- runAll (Om.expandErr (Om.fatal "fatal" :: Om Config () Int)) <#> (_ <> "?")
  log sixth # liftEffect
  seventh <- runAll (Om.inParallel [ combined 1, combined 2, combined 4 ] # Om.expand)
  log seventh # liftEffect
