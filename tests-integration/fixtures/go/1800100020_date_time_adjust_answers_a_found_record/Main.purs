module Main where

import Prelude

import Data.Date (canonicalDate)
import Data.DateTime (DateTime(..), adjust)
import Data.Enum (toEnum)
import Data.Maybe (Maybe, fromJust, isJust)
import Data.Time (Time(..))
import Data.Time.Duration (Days(..), Hours(..), Milliseconds(..), Minutes(..))
import Effect (Effect)
import Journal (log)
import Partial.Unsafe (unsafePartial)

dateTime :: Int -> Int -> Int -> Int -> Int -> Int -> Int -> DateTime
dateTime y mo d h mi s ms = unsafePartial do
  let date = canonicalDate (fromJust (toEnum y)) (fromJust (toEnum mo)) (fromJust (toEnum d))
  DateTime date (Time (fromJust (toEnum h)) (fromJust (toEnum mi)) (fromJust (toEnum s)) (fromJust (toEnum ms)))

newYear :: DateTime
newYear = dateTime 2026 12 31 0 0 0 0

shown :: Maybe DateTime -> String
shown = show

main :: Effect Unit
main = do
  log (show (adjust (Days 1.0) newYear))
  log (shown (adjust (Hours 24.5) newYear))
  log (shown (adjust (Days (-1.0)) (dateTime 2024 3 1 0 0 0 0)))
  log (shown (adjust (Minutes (-1.0)) (dateTime 2000 1 1 0 0 0 0)))
  log (shown (adjust (Milliseconds 1.7) (dateTime 2000 1 1 0 0 0 999)))
  log (shown (adjust (Milliseconds (-0.5)) (dateTime 2000 1 1 0 0 0 0)))
  log (shown (adjust (Days 365.0) (dateTime 50 6 15 12 30 0 0)))
  log (shown (adjust (Days (-20000.0)) (dateTime 1970 1 1 0 0 0 0)))
  log (shown (adjust (Days 1.0e9) newYear))
  log (shown (adjust (Days (-1.0e9)) newYear))
  log (shown (adjust (Days 1.0) (dateTime 275759 12 31 0 0 0 0)))
  log (shown (adjust (Days (-1.0)) (dateTime (-271820) 1 1 0 0 0 0)))
  log (show (isJust (adjust (Milliseconds 0.0) newYear)))
