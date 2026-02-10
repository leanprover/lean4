/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

module
prelude
public import Init.Core
import Init.Data.Bool
import Init.ByCases
import Init.Classical

public section

namespace DerivingHelpers

macro "deriving_ReflEq_tactic" : tactic => `(tactic|(
  intro x
  induction x
  all_goals
    simp only [ BEq.refl, ↓reduceDIte, Bool.and_true, *, reduceBEq ,reduceCtorIdx]
))

theorem and_true_curry {a b : Bool} {P : Prop}
    (h : a → b → P) : (a && b) → P := by
  rw [Bool.and_eq_true_iff]
  intro h'
  apply h h'.1 h'.2


theorem deriving_lawful_beq_helper_dep {x y : α} [BEq α] [ReflBEq α]
  {t : (x == y) = true → Bool} {P : Prop}
    (inst : (x == y) = true → x = y)
    (k : (h : x = y) → t (h ▸ ReflBEq.rfl) = true → P) :
    (if h : (x == y) then t h else false) = true → P := by
  intro h
  by_cases hxy : x = y
  · subst hxy
    apply k rfl
    rw [dif_pos (BEq.refl x)] at h
    exact h
  · by_cases hxy' : x == y
    · exact False.elim <| hxy (inst hxy')
    · rw [dif_neg hxy'] at h
      contradiction

theorem deriving_lawful_beq_helper_nd {x y : α} [BEq α] [ReflBEq α]
    {P : Prop}
    (inst : (x == y) = true → x = y)
    (k : x = y → P) :
    (x == y) = true → P := by
  intro h
  by_cases hxy : x = y
  · subst hxy
    apply k rfl
  · exact False.elim <| hxy (inst h)

end DerivingHelpers

syntax "deriving_LawfulEq_tactic_step" : tactic
macro_rules
| `(tactic| deriving_LawfulEq_tactic_step) =>
  `(tactic| fail "deriving_LawfulEq_tactic_step failed")
macro_rules
| `(tactic| deriving_LawfulEq_tactic_step) =>
  `(tactic| ( with_reducible change dite (_ == _) _ _ = true → _
              refine DerivingHelpers.deriving_lawful_beq_helper_dep ?_ ?_
              · solve | apply_assumption | simp | fail "could not discharge eq_of_beq assumption"
              intro h
              cases h
              dsimp only
    ))
macro_rules
| `(tactic| deriving_LawfulEq_tactic_step) =>
  `(tactic| ( with_reducible change (_ == _) = true → _
              refine DerivingHelpers.deriving_lawful_beq_helper_nd ?_ ?_
              · solve | apply_assumption | simp | fail "could not discharge eq_of_beq assumption"
              intro h
              subst h
    ))
macro_rules
| `(tactic| deriving_LawfulEq_tactic_step) =>
  `(tactic| ( with_reducible change (_ == _ && _) = true → _
              refine DerivingHelpers.and_true_curry ?_))
macro_rules
| `(tactic| deriving_LawfulEq_tactic_step) =>
  `(tactic| rfl)
macro_rules
| `(tactic| deriving_LawfulEq_tactic_step) =>
  `(tactic| intro _; trivial)

macro "deriving_LawfulEq_tactic" : tactic => `(tactic|(
  intro x
  induction x
  all_goals
    intro y
    cases y
    all_goals
      simp only [reduceBEq, reduceCtorIdx]
      repeat deriving_LawfulEq_tactic_step
))
