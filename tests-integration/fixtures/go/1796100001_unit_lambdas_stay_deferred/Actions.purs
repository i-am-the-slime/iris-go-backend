module Actions where

import Effect (Effect)

-- | Runs the action it is given, which Go code receives as a function it calls when it chooses.
foreign import runWhenAsked :: Effect Int -> Effect Int
