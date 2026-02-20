import Lean
open Lean
open Lean.Elab
open Lean.Meta
open Lean.Elab.Tactic

/--
trace: a b c : Nat
h₁ : a = b
h₂ : b = c
⊢ a = b
-/
#guard_msgs in
example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by
  apply Eq.trans _ h₂  -- the metavars created during elaboration become new goals
  trace_state
  exact h₁

/--
trace: case h
a : Nat
⊢ ?w = a

case w
a : Nat
⊢ Nat
-/
#guard_msgs in
example (a : Nat) : ∃ x, x = a := by
  apply Exists.intro  -- the goal for the witness should occur "after" the goal for x = a
  trace_state
  rfl

elab "fapply " e:term : tactic =>
  evalApplyLikeTactic (MVarId.apply (cfg := {newGoals := ApplyNewGoals.all})) e

elab "eapply " e:term : tactic =>
  evalApplyLikeTactic (MVarId.apply (cfg := {newGoals := ApplyNewGoals.nonDependentOnly})) e

/--
trace: case h
a : Nat
⊢ ?w = a
-/
#guard_msgs in
example (a : Nat) : ∃ x, x = a := by
  eapply Exists.intro  -- only metavars with out forward dependencies are added as goals.
  trace_state
  rfl

/--
trace: case w
a : Nat
⊢ Nat

case h
a : Nat
⊢ ?w = a
---
trace: case h
a : Nat
⊢ a = a
-/
#guard_msgs in
example (a : Nat) : ∃ x, x = a := by
  fapply Exists.intro  -- all unassigned metavars are added as new goals using the order they were created.
  trace_state
  exact a
  trace_state
  rfl
