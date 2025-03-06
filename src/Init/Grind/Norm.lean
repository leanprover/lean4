/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.SimpLemmas
import Init.PropLemmas
import Init.Classical
import Init.ByCases
import Init.Data.Int.Linear

namespace Lean.Grind
/-!
Normalization theorems for the `grind` tactic.
-/

theorem iff_eq (p q : Prop) : (p ↔ q) = (p = q) := by
  by_cases p <;> by_cases q <;> simp [*]

theorem eq_true_eq (p : Prop) : (p = True) = p := by simp
theorem eq_false_eq (p : Prop) : (p = False) = ¬p := by simp
theorem not_eq_prop (p q : Prop) : (¬(p = q)) = (p = ¬q) := by
  by_cases p <;> by_cases q <;> simp [*]

-- Remark: we disabled the following normalization rule because we want this information when implementing splitting heuristics
-- Implication as a clause
theorem imp_eq (p q : Prop) : (p → q) = (¬ p ∨ q) := by
  by_cases p <;> by_cases q <;> simp [*]

theorem true_imp_eq (p : Prop) : (True → p) = p := by simp
theorem false_imp_eq (p : Prop) : (False → p) = True := by simp
theorem imp_true_eq (p : Prop) : (p → True) = True := by simp
theorem imp_false_eq (p : Prop) : (p → False) = ¬p := by simp
theorem imp_self_eq (p : Prop) : (p → p) = True := by simp

theorem not_and (p q : Prop) : (¬(p ∧ q)) = (¬p ∨ ¬q) := by
  by_cases p <;> by_cases q <;> simp [*]

theorem not_ite {_ : Decidable p} (q r : Prop) : (¬ite p q r) = ite p (¬q) (¬r) := by
  by_cases p <;> simp [*]

theorem ite_true_false {_ : Decidable p} : (ite p True False) = p := by
  by_cases p <;> simp

theorem ite_false_true {_ : Decidable p} : (ite p False True) = ¬p := by
  by_cases p <;> simp

theorem not_forall (p : α → Prop) : (¬∀ x, p x) = ∃ x, ¬p x := by simp

theorem not_exists (p : α → Prop) : (¬∃ x, p x) = ∀ x, ¬p x := by simp

theorem cond_eq_ite (c : Bool) (a b : α) : cond c a b = ite c a b := by
  cases c <;> simp [*]

theorem Nat.lt_eq (a b : Nat) : (a < b) = (a + 1 ≤ b) := by
  simp [Nat.lt, LT.lt]

theorem Int.lt_eq (a b : Int) : (a < b) = (a + 1 ≤ b) := by
  simp [Int.lt, LT.lt]

theorem ge_eq [LE α] (a b : α) : (a ≥ b) = (b ≤ a) := rfl
theorem gt_eq [LT α] (a b : α) : (a > b) = (b < a) := rfl

theorem beq_eq_decide_eq {_ : BEq α} [LawfulBEq α] [DecidableEq α] (a b : α) : (a == b) = (decide (a = b)) := by
  by_cases a = b
  next h => simp [h]
  next h => simp [beq_eq_false_iff_ne.mpr h, decide_eq_false h]

theorem bne_eq_decide_not_eq {_ : BEq α} [LawfulBEq α] [DecidableEq α] (a b : α) : (a != b) = (decide (¬ a = b)) := by
  by_cases a = b <;> simp [*]

init_grind_norm
  /- Pre theorems -/
  not_and not_or not_ite not_forall not_exists
  /- Nat relational ops neg -/
  Nat.not_ge_eq Nat.not_le_eq
  |
  /- Post theorems -/
  Classical.not_not
  ne_eq iff_eq eq_self heq_eq_eq
  -- Prop equality
  eq_true_eq eq_false_eq not_eq_prop
  -- True
  not_true
  -- False
  not_false_eq_true
  -- Implication
  true_imp_eq false_imp_eq imp_true_eq imp_false_eq imp_self_eq
  -- And
  and_true true_and and_false false_and and_assoc
  -- Or
  or_true true_or or_false false_or or_assoc
  -- ite
  ite_true ite_false ite_true_false ite_false_true
  -- Forall
  forall_and
  -- Exists
  exists_const exists_or exists_prop exists_and_left exists_and_right
  -- Bool cond
  cond_eq_ite
  -- Bool or
  Bool.or_false Bool.or_true Bool.false_or Bool.true_or Bool.or_eq_true Bool.or_assoc
  -- Bool and
  Bool.and_false Bool.and_true Bool.false_and Bool.true_and Bool.and_eq_true Bool.and_assoc
  -- Bool not
  Bool.not_not
  -- beq
  beq_iff_eq beq_eq_decide_eq
  -- bne
  bne_iff_ne bne_eq_decide_not_eq
  -- Bool not eq true/false
  Bool.not_eq_true Bool.not_eq_false
  -- decide
  decide_eq_true_eq decide_not not_decide_eq_true
  -- Nat LE
  Nat.le_zero_eq
  -- Nat/Int LT
  Nat.lt_eq
  -- Nat.succ
  Nat.succ_eq_add_one
  -- Nat op folding
  Nat.add_eq Nat.sub_eq Nat.mul_eq Nat.zero_eq Nat.le_eq
  -- Int
  Int.lt_eq
  Int.emod_neg Int.ediv_zero Int.emod_zero
  -- GT GE
  ge_eq gt_eq
  -- Int op folding
  Int.add_def Int.mul_def
  Int.Linear.sub_fold Int.Linear.neg_fold
  -- Int divides
  Int.one_dvd Int.zero_dvd

end Lean.Grind
