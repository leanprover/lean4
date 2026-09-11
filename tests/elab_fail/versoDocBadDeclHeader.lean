import Lean

/-!
A declaration whose header does not parse reports that error even when the declaration's body
contains a Verso docstring.
-/

set_option doc.verso true

inductive 1Foo where
  /-- A *valid* doc. -/
  | a
