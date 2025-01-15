import Lean.Elab.Command
import Lean.Elab.Syntax

open Lean.Elab.Term.toParserDescr (isValidAtom)
open Lean Elab Command

/-!
Test various classes of atoms that should be allowed or not.
-/

def test (expected : Bool) (strings : List String) : CommandElabM Unit := Id.run do
  let mut wrong : List String := []
  for s in strings do
    if isValidAtom s != expected then
      wrong := s :: wrong
    if isValidAtom (" " ++ s) != expected then
      wrong := s!"{s} (with leading whitespace)" :: wrong
    if isValidAtom (s ++ " ") != expected then
      wrong := s!"{s} (with trailing whitespace)" :: wrong
    if isValidAtom (" " ++ s ++ " ") != expected then
      wrong := s!"{s} (with leading and trailing whitespace)" :: wrong

  if wrong.isEmpty then
    logInfo <| "All " ++ if expected then "accepted" else "rejected"
  else
    logError <|
      s!"The following atoms should be {if expected then "" else "in"}valid but are not:\n" ++
      String.join (wrong.reverse.map (s! " * {·}\n"))


syntax "#test_valid" term : command
syntax "#test_invalid" term : command

macro_rules
  | `(#test_valid%$tok $t) => `(#eval%$tok test true $t)
  | `(#test_invalid%$tok $t) => `(#eval%$tok test false $t)


/-!
# No Empty Atoms
-/

/-- info: All rejected -/
#guard_msgs in
#test_invalid [""]


/-!
# Preventing Character Literal Confusion

Atoms are required to be suitably unlike character literals. This means that if they start with a
single quote, the next character must also be a single quote.

Two single quotes (and variations on it) has long-term usage as an infix operator in Mathlib.
-/

/-- info: All accepted -/
#guard_msgs in
#test_valid ["if", "''", "''ᵁ", "if'", "x'y'z", "x''y"]

/-- info: All rejected -/
#guard_msgs in
#test_invalid ["'x'", "'ᵁ", "'c", "'no'", "'"]


/-!
# No Internal Whitespace
-/

/-- info: All rejected -/
#guard_msgs in
#test_invalid ["open mixed", "open   mixed"]


/-!
# No Confusion with String Literals

Internal double quotes are allowed.
-/

/-- info: All accepted -/
#guard_msgs in
#test_valid ["what\"string\"is_this?"]

/-- info: All rejected -/
#guard_msgs in
#test_invalid ["\"","\"\"", "\"f\""]

/-!
# No Confusion with Escaped Identifiers

This doesn't confuse the parser, but it may confuse a user if they can define an atom that can never
be parsed.
-/

/-- info: All accepted -/
#guard_msgs in
#test_valid ["prefix«", "prefix«test", "prefix«test»", "prefix«test»foo"]

/-- info: All rejected -/
#guard_msgs in
#test_invalid ["«", "«test", "«test»", "«test»foo"]


/-!
# No Confusion with Name Literals

The first two characters of an atom may not be a valid start of a name literal
-/

/-- info: All accepted -/
#guard_msgs in
#test_valid ["``", "`!", "x`"]

/-!
The next set all begin with U0x2035, REVERSED PRIME, rather than back-tick, and are thus accepted.
-/
/-- info: All accepted -/
#guard_msgs in
#test_valid ["‵", "‵x", "‵«", "‵xyz", "‵«x.y", "‵«x.y.z»"]


/-- info: All rejected -/
#guard_msgs in
#test_invalid ["`", "`x", "`«", "`xyz", "`«x.y", "`«x.y.z»"]


/-!
# No Leading Digits
-/

/-- info: All accepted -/
#guard_msgs in
#test_valid ["prefix5", "prefix22test", "prefix1test0", "prefix8test8foo"]

/-- info: All rejected -/
#guard_msgs in
#test_invalid ["0", "1test", "0test3"]
