module

import Lean

/-! # Pretty-printing `choice` nodes from duplicate syntax declarations

Declaring the same syntax twice makes the parser pack both parses into a `choice` node.
Formatting one alternative must leave the cursor where formatting an ordinary node would;
otherwise the backtrack escapes as `format: uncaught backtrack exception`, or is swallowed by
a `sepByIndent` separator and silently drops the rest of the sequence. Regression test for
https://github.com/leanprover/lean4/issues/14611.
-/

open Lean PrettyPrinter

/-- Pretty-print command source at the given width. -/
def ppCommand (src : String) (width : Nat := 100) : CoreM String := do
  match Parser.runParserCategory (← getEnv) `command src "<test>" with
  | .error e => throwError e
  | .ok stx => return (← ppCategory `command stx).pretty width

syntax "GG" : term
syntax "GG" : term

-- a binder whose whole type is the ambiguous notation used to throw
-- `format: uncaught backtrack exception`
/--
info: def foo (y : GG) : Nat :=
  0
-/
#guard_msgs in
#eval show CoreM Unit from do
  IO.println (← ppCommand "def foo (y : GG) : Nat := 0")

-- conclusion and body positions formatted before; guard against regressions
/--
info: def bar : GG :=
  0
-/
#guard_msgs in
#eval show CoreM Unit from do
  IO.println (← ppCommand "def bar : GG := 0")

-- an unambiguous binder of the same shape is unaffected
/--
info: def baz (y : Nat) : Nat :=
  0
-/
#guard_msgs in
#eval show CoreM Unit from do
  IO.println (← ppCommand "def baz (y : Nat) : Nat := 0")

-- inside a tactic sequence the backtrack was swallowed by the `sepByIndent` separator,
-- silently dropping the remainder of the sequence
/--
info: example (X Y : Nat) : True := by
  have h : ∃ y : GG, y = y := ⟨_, rfl⟩
  trivial
-/
#guard_msgs in
#eval show CoreM Unit from do
  IO.println (← ppCommand
    "example (X Y : Nat) : True := by\n  have h : ∃ y : GG, y = y := ⟨_, rfl⟩\n  trivial")
