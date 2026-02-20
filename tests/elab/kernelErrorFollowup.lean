import Lean.Elab.Tactic.Basic

/-!
Kernel errors should not lead to follow-up errors but should be detectable using `#print axioms`.
-/

/-- error: (kernel) declaration has metavariables 'bad' -/
#guard_msgs in
def bad : Empty := by
  run_tac do Lean.Elab.Tactic.popMainGoal

theorem zero_eq_one : 0 = 1 := bad.elim

/--
info: def bad : Empty :=
?_uniq.4
-/
#guard_msgs in
set_option pp.raw true in
#print bad

/--
info: theorem zero_eq_one : 0 = 1 :=
Empty.elim bad
-/
#guard_msgs in
#print zero_eq_one

/-- info: 'zero_eq_one' depends on axioms: [bad] -/
#guard_msgs in
#print axioms zero_eq_one
