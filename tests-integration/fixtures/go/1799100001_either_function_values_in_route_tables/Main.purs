module Main where

import Prelude

import Control.Monad.Error.Class (throwError)
import Control.Monad.Except (ExceptT, runExceptT)
import Data.Array ((!!))
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Class (liftEffect)
import Journal (log)

data Problem = Negative Int | TooLarge Int

instance Show Problem where
  show (Negative n) = "Negative " <> show n
  show (TooLarge n) = "TooLarge " <> show n

type Handler = Int -> ExceptT Problem Effect Int

type Routes = { handlers :: Array Handler, fallback :: Handler }

double :: Handler
double n
  | n > 100 = throwError (TooLarge n)
  | otherwise = pure (n * 2)

routes :: Routes
routes =
  { handlers:
      [ \n -> if n < 0 then throwError (Negative n) else pure (n + 1)
      , double
      , \n -> do
          liftEffect (log ("third sees " <> show n))
          pure (n - 1)
      ]
  , fallback: \n -> pure n
  }

route :: Routes -> Int -> Int -> ExceptT Problem Effect Int
route table index n = do
  let
    handler = case table.handlers !! index of
      Just found -> found
      Nothing -> table.fallback
  a <- handler n
  b <- handler (a + 1)
  pure (a + b)

main :: Effect Unit
main = for_ [ 0, 1, 2, 3 ] \index -> for_ [ -5, 7, 80 ] \n -> do
  result <- runExceptT (route routes index n)
  log (show index <> " " <> show n <> ": " <> show result)
