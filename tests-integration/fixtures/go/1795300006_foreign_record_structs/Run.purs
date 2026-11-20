module Run where

import Effect (Effect)

type Output = { stdout :: String, stderr :: String, exitCode :: Int }

foreign import run :: String -> Effect Output
foreign import runAll :: Array String -> Effect (Array Output)
foreign import describe :: Output -> String
