module Bench.Om.App where

import Prelude

import Bench.Harness (benchmarkAff)
import Data.Array ((..))
import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Tuple.Nested ((/\))
import Data.String as String
import Data.Traversable (for)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Yoga.Om (Om, ask, asks)
import Yoga.Om as Om

hypothesis :: String
hypothesis = "a request pipeline of a few Om layers (config and a metrics Ref in the context, Map lookups via note, typed errors handled per request) pays Om's CPS binds, Variant dispatch and Effect lifting together"

main :: Effect Unit
main = benchmarkAff { size: 12000, workload }

type Config = { discountPercent :: Int, maximumQuantity :: Int, currency :: String }

type Context = { config :: Config, users :: Map Int User, metrics :: Ref Metrics }

type User = { name :: String, tier :: Int, blocked :: Boolean }

type Metrics = { served :: Int, rejected :: Int, missing :: Int }

type Request = { userId :: Int, quantity :: Int, unitPrice :: Int }

type RequestErrors r = (userNotFound :: Int, userBlocked :: String, invalidQuantity :: { quantity :: Int, maximum :: Int } | r)

workload :: Int -> Aff String
workload n = do
  metrics <- Ref.new { served: 0, rejected: 0, missing: 0 } # liftEffect
  responses <- serveAll (1 .. n) # Om.runOm (context metrics) { exception: \_ -> pure [] }
  final <- Ref.read metrics # liftEffect
  pure (summary responses final)
  where
  context metrics = { config: { discountPercent: 15, maximumQuantity: 40, currency: "EUR" }, users, metrics }

  users = Map.fromFoldable (map (\i -> i /\ user i) (1 .. 500))
    where
    user i = { name: "user" <> show i, tier: i `mod` 4, blocked: i `mod` 37 == 0 }

  summary responses final = String.joinWith " "
    [ show (Array.length responses)
    , show (foldl (\total response -> (total + String.length response) `mod` 1000003) 0 responses)
    , show final.served
    , show final.rejected
    , show final.missing
    ]

serveAll :: Array Int -> Om Context () (Array String)
serveAll ids = for ids \i -> serve (request i)
  where
  request i = { userId: (i * 7) `mod` 523, quantity: (i * 13) `mod` 47, unitPrice: 100 + i `mod` 50 }

serve :: Request -> Om Context () String
serve request = handle request
  # Om.handleErrors
      { userNotFound: \userId -> record (\m -> m { missing = m.missing + 1 }) $> ("missing " <> show userId)
      , userBlocked: \name -> record (\m -> m { rejected = m.rejected + 1 }) $> ("blocked " <> name)
      , invalidQuantity: \{ quantity, maximum } -> record (\m -> m { rejected = m.rejected + 1 }) $> (show quantity <> ">" <> show maximum)
      }

handle :: Request -> Om Context (RequestErrors ()) String
handle request = do
  user <- findUser request.userId
  quantity <- validQuantity request.quantity
  total <- price user quantity request.unitPrice
  record (\m -> m { served = m.served + 1 })
  { config: { currency } } <- ask
  pure (user.name <> ": " <> show total <> " " <> currency)

findUser :: forall r. Int -> Om Context (RequestErrors r) User
findUser userId = do
  users <- asks _.users
  user <- Map.lookup userId users # Om.note { userNotFound: userId }
  Om.throwWhen { userBlocked: user.name } user.blocked
  pure user

validQuantity :: forall r. Int -> Om Context (RequestErrors r) Int
validQuantity quantity = do
  maximum <- asks _.config.maximumQuantity
  Om.throwUnless { invalidQuantity: { quantity, maximum } } (quantity > 0 && quantity <= maximum)
  pure quantity

price :: forall r. User -> Int -> Int -> Om Context r Int
price user quantity unitPrice = do
  discount <- asks _.config.discountPercent
  let gross = quantity * unitPrice
  pure (gross - (gross * discount * user.tier) / 300)

record :: forall r. (Metrics -> Metrics) -> Om Context r Unit
record change = do
  metrics <- asks _.metrics
  Ref.modify_ change metrics # liftEffect
