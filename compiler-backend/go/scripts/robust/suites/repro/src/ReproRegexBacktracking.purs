module ReproRegexBacktracking where
import Prelude
import Data.Either (either)
import Data.String.Regex (Regex, match, regex, replace, search, split, test)
import Data.String.Regex.Flags (global, noFlags)
import Effect (Effect)
import Effect.Console (log)
-- Backreferences and lookaround, which RE2 cannot express, behave as JavaScript's RegExp.
main :: Effect Unit
main = do
  withRegex "(\\w)\\1" global \rx -> log (replace rx "<$&>" "aabbcd")
  withRegex "(?<q>['\"])(.*?)\\k<q>" global \rx -> log (replace rx "[$2]" "say 'hi' and \"yo\"")
  withRegex "\\d+(?=px)" global \rx -> log (show (match rx "10px 20em 30px"))
  withRegex "(?<!b)a" global \rx -> log (replace rx "A" "banana")
  withRegex "(?<=\\$)\\d+(\\.\\d\\d)?" noFlags \rx -> log (show (match rx "cost: $10.50"))
  withRegex "^(?:(?!ab).)*$" noFlags \rx -> log (show [ test rx "xay", test rx "xaby" ])
  withRegex "(a)(?<n>b)(c)\\k<n>\\2" noFlags \rx -> log (show (match rx "xabcbb"))
  withRegex "(?=a)" noFlags \rx -> log (show (split rx "banana") <> " " <> show (search rx "banana"))
  where
  withRegex :: String -> _ -> (Regex -> Effect Unit) -> Effect Unit
  withRegex source flags use = either (\error -> log ("error: " <> error)) use (regex source flags)
