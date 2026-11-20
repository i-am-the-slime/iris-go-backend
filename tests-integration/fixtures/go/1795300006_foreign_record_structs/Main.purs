module Main where

import Prelude

import Data.Array (length)
import Effect (Effect)
import Run (Output, describe, run, runAll)

-- | A struct in a module's Go file named like one of its record synonyms is that record: the
-- program builds, reads, updates and matches it, and passes it to and from foreign functions as
-- it is.
main :: Effect (Array String)
main = do
  output <- run "echo"
  outputs <- runAll [ "a", "b" ]
  let louder = output { stdout = output.stdout <> "!" }
  pure
    [ describe louder
    , describe made
    , show (length outputs)
    , case louder of
        { exitCode, stderr } -> stderr <> show exitCode
    ]

made :: Output
made = { stdout: "made", stderr: "", exitCode: 3 }
