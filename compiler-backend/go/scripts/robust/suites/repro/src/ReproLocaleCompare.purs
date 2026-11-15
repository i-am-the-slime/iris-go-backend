module ReproLocaleCompare where
import Prelude
import Data.Array (sortBy)
import Data.String (joinWith, localeCompare)
import Effect (Effect)
import Effect.Console (log)
-- localeCompare is ICU's root collation beyond Latin-1 too.
main :: Effect Unit
main = do
  let words = [ "z", "ł", "ą", "b", "½", "2", "²", "ﬁ", "fi", "ß", "ss", "st", "þ", "ı", "i", "ǅ", "co-op", "coop", "co op", "ё", "я", "\x200B", "", "\xD800", "\xE000", "\xFFFD", "résumé", "resume", "Resume" ]
  log (joinWith " " (sortBy localeCompare words))
  log (show (map (localeCompare "a\x301") [ "á", "a", "b" ]))
