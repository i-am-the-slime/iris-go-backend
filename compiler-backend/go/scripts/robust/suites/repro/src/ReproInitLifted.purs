module ReproInitLifted where
import Prelude
import Data.Array as Array
import Data.Maybe (Maybe(..), fromJust)
import Effect (Effect)
import Effect.Console (log)
import Partial.Unsafe (unsafeCrashWith, unsafePartial)
-- Crashing expressions inside functions run only when the function does; main never takes the
-- crashing branch, so nothing may evaluate them while the program loads.
positive :: Int -> Int
positive n = if n > 0 then n else unsafeCrashWith "not positive"
first :: Array Int -> Int
first xs = unsafePartial (fromJust (Array.head xs))
fallback :: Int -> Int
fallback n = case n of
  0 -> unsafePartial (fromJust Nothing)
  _ -> n
main :: Effect Unit
main = do
  log (show (positive 3))
  log (show (first [ 4 ]))
  log (show (fallback 5))
