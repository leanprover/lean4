import Lean.PrettyPrinter.Source

-- Test that multiline string content is preserved (no extra indentation)
open Lean PrettyPrinter in
/--
info: #eval "Hello
world"
-/
#guard_msgs in
#eval do
  let input := "#eval \"Hello\nworld\"\n"
  let result ← ppSource input "<test>"
  IO.println result

-- Test that formatting multiline strings is idempotent
open Lean PrettyPrinter in
/-- info: true -/
#guard_msgs in
#eval do
  let input := "#eval \"Hello\nworld\"\n"
  let result ← ppSource input "<test>"
  let result2 ← ppSource result "<test>"
  IO.println (result == result2)

-- Test multiline string in a definition
open Lean PrettyPrinter in
/--
info: def greeting :=
  "Hello
world"
-/
#guard_msgs in
#eval do
  let input := "def greeting := \"Hello\nworld\"\n"
  let result ← ppSource input "<test>"
  IO.println result

-- Test interpolated multiline string
open Lean PrettyPrinter in
/--
info: def greeting (name : String) :=
  s! "Hello
{name}"
-/
#guard_msgs in
#eval do
  let input := "def greeting (name : String) := s!\"Hello\n{name}\"\n"
  let result ← ppSource input "<test>"
  IO.println result
