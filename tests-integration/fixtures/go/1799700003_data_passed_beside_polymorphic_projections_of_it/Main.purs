module Main where

import Prelude

import Data.Function.Uncurried (runFn3)
import Effect (Effect)
import Entries (joinEntriesImpl)
import Journal (log)

data Entry a b = Entry a b

entryKey :: forall a b. Entry a b -> a
entryKey (Entry key _) = key

entryCount :: forall a b. Entry a b -> b
entryCount (Entry _ count) = count

joinEntries :: Array (Entry String Int) -> String
joinEntries entries = runFn3 joinEntriesImpl entryKey entryCount entries

main :: Effect Unit
main = log (joinEntries [ Entry "apples" 3, Entry "pears" 5 ])
