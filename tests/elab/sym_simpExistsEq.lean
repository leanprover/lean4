import Lean

/-!
# `Sym.Simp.simpExistsEq`

The opt-in `Sym.Simp.simpExistsEq` post-simproc rewrites `∃ x, x = a` and `∃ x, a = x` to `True`,
and `∃ x, x = a ∧ p x` (and its three symmetric variants) to `p a`.
-/

namespace SymSimpExistsEq
open Lean Meta Elab Lean.Elab.Tactic.Grind

/-- Simplifies the main goal with `Sym.Simp.simpExistsEq` as the only post-method, failing if it
makes no progress. -/
syntax (name := exEq) "ex_eq" : grind

@[grind_tactic exEq] def evalExEq : GrindTactic := fun _ => do
  let goal ← getMainGoal
  if ← simpMainGoal { post := Sym.Simp.simpExistsEq } then return
  if (← getMainGoal).mvarId == goal.mvarId then
    throwError "ex_eq: no progress"

opaque P : Nat → Prop
abbrev MyNat := Nat
universe u

/-! ## The six shapes -/

theorem eqLeft (a : Nat) : ∃ x, x = a := by sym => ex_eq
theorem eqRight (a : Nat) : ∃ x, a = x := by sym => ex_eq
theorem eqLeftAnd (a : Nat) (h : P a) : ∃ x, x = a ∧ P x := by sym => ex_eq; exact h
theorem eqRightAnd (a : Nat) (h : P a) : ∃ x, a = x ∧ P x := by sym => ex_eq; exact h
theorem andEqLeft (a : Nat) (h : P a) : ∃ x, P x ∧ x = a := by sym => ex_eq; exact h
theorem andEqRight (a : Nat) (h : P a) : ∃ x, P x ∧ a = x := by sym => ex_eq; exact h

/-! ## Universe-polymorphic and `Prop` witnesses -/

theorem sortU {α : Sort u} (a : α) : ∃ x, x = a := by sym => ex_eq
theorem typeU {α : Type u} (a : α) (Q : α → Prop) (h : Q a) : ∃ x, Q x ∧ a = x := by
  sym => ex_eq; exact h
theorem propWitness (p : Prop) (a : p) : ∃ x : p, x = a := by sym => ex_eq

/-! ## The equality's type differs syntactically from the binder type -/

theorem eqAtAbbrev (a : Nat) : ∃ x : Nat, @Eq MyNat x a := by sym => ex_eq

/-! ## Function-typed witness applied in the remaining conjunct -/

theorem funWitness (g : Nat → Nat) (h : g 0 = 0) : ∃ f : Nat → Nat, f = g ∧ f 0 = 0 := by
  sym => ex_eq; exact h

/-! ## Nested existentials -/

theorem nested (a b : Nat) (h : a = b) : ∃ x, x = a ∧ ∃ y, y = b ∧ x = y := by
  sym => ex_eq; exact h

/-! ## Does not fire when the witness mentions the bound variable -/

/-- error: ex_eq: no progress -/
#guard_msgs in
theorem dependentWitness (f : Nat → Nat) : ∃ x, x = f x := by sym => ex_eq

end SymSimpExistsEq
