/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
prelude
import Init.Classical

/-! # by_cases tactic and if-then-else support -/

/--
`by_cases (h :)? p` splits the main goal into two cases, assuming `h : p` in the first branch, and `h : ¬ p` in the second branch.
-/
syntax "by_cases " (atomic(ident " : "))? term : tactic

macro_rules
  | `(tactic| by_cases $e) => `(tactic| by_cases h : $e)
macro_rules
  | `(tactic| by_cases $h : $e) =>
    `(tactic| open Classical in refine if $h:ident : $e then ?pos else ?neg)

/-! ## if-then-else -/

@[simp] theorem if_true {_ : Decidable True} (t e : α) : ite True t e = t := if_pos trivial

@[simp] theorem if_false {_ : Decidable False} (t e : α) : ite False t e = e := if_neg id

theorem ite_id [Decidable c] {α} (t : α) : (if c then t else t) = t := by split <;> rfl

/-- A function applied to a `dite` is a `dite` of that function applied to each of the branches. -/
theorem apply_dite (f : α → β) (P : Prop) [Decidable P] (x : P → α) (y : ¬P → α) :
    f (dite P x y) = dite P (fun h => f (x h)) (fun h => f (y h)) := by
  by_cases h : P <;> simp [h]

/-- A function applied to a `ite` is a `ite` of that function applied to each of the branches. -/
theorem apply_ite (f : α → β) (P : Prop) [Decidable P] (x y : α) :
    f (ite P x y) = ite P (f x) (f y) :=
  apply_dite f P (fun _ => x) (fun _ => y)

/-- A `dite` whose results do not actually depend on the condition may be reduced to an `ite`. -/
@[simp] theorem dite_eq_ite [Decidable P] :
  (dite P (fun _ => a) (fun _ => b)) = ite P a b := rfl

@[deprecated "Use `ite_eq_right_iff`" (since := "2024-09-18")]
theorem ite_some_none_eq_none [Decidable P] :
    (if P then some x else none) = none ↔ ¬ P := by
  simp only [ite_eq_right_iff, reduceCtorEq]
  rfl

@[deprecated "Use `Option.ite_none_right_eq_some`" (since := "2024-09-18")]
theorem ite_some_none_eq_some [Decidable P] :
    (if P then some x else none) = some y ↔ P ∧ x = y := by
  split <;> simp_all

@[deprecated "Use `dite_eq_right_iff" (since := "2024-09-18")]
theorem dite_some_none_eq_none [Decidable P] {x : P → α} :
    (if h : P then some (x h) else none) = none ↔ ¬P := by
  simp

@[deprecated "Use `Option.dite_none_right_eq_some`" (since := "2024-09-18")]
theorem dite_some_none_eq_some [Decidable P] {x : P → α} {y : α} :
    (if h : P then some (x h) else none) = some y ↔ ∃ h : P, x h = y := by
  by_cases h : P <;> simp [h]
