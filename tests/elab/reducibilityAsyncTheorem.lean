import Lean
open Lean

/-!
Tests that the reducibility status of asynchronously elaborated theorems, and of declarations nested
in them, is read from the right environment branch.
-/

set_option Elab.async true

theorem plain : True := trivial

/-- info: Lean.ReducibilityStatus.semireducible -/
#guard_msgs in
run_cmd logInfo m!"{repr (← getReducibilityStatus ``plain)}"

section
set_option allowUnsafeReducibility true

@[reducible] theorem onDecl : True := trivial

/-- info: Lean.ReducibilityStatus.reducible -/
#guard_msgs in
run_cmd logInfo m!"{repr (← getReducibilityStatus ``onDecl)}"

theorem afterDecl : True := trivial
attribute [irreducible] afterDecl

/-- info: Lean.ReducibilityStatus.irreducible -/
#guard_msgs in
run_cmd logInfo m!"{repr (← getReducibilityStatus ``afterDecl)}"
end

theorem withAux : (match 1 with | 0 => 0 | n + 1 => n) = 0 := by
  have _ := aux 1
  rfl
where
  @[reducible] aux (n : Nat) : Nat := n

/-- info: Lean.ReducibilityStatus.reducible -/
#guard_msgs in
run_cmd logInfo m!"{repr (← getReducibilityStatus ``withAux.aux)}"

/-- info: Lean.ReducibilityStatus.semireducible -/
#guard_msgs in
run_cmd logInfo m!"{repr (← getReducibilityStatus ``withAux)}"
