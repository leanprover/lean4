/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.SimpLemmas
import Init.Classical
import Init.ByCases

namespace Lean.Grind
/-!
Normalization theorems for the `grind` tactic.

We are also going to use simproc's in the future.
-/

-- Not
attribute [grind_norm] Classical.not_not

-- Ne
attribute [grind_norm] ne_eq

-- Iff
@[grind_norm] theorem iff_eq (p q : Prop) : (p ↔ q) = (p = q) := by
  by_cases p <;> by_cases q <;> simp [*]

-- Eq
attribute [grind_norm] eq_self heq_eq_eq

-- Prop equality
@[grind_norm] theorem eq_true_eq (p : Prop) : (p = True) = p := by simp
@[grind_norm] theorem eq_false_eq (p : Prop) : (p = False) = ¬p := by simp
@[grind_norm] theorem not_eq_prop (p q : Prop) : (¬(p = q)) = (p = ¬q) := by
  by_cases p <;> by_cases q <;> simp [*]

-- True
attribute [grind_norm] not_true

-- False
attribute [grind_norm] not_false_eq_true

-- Implication as a clause
@[grind_norm] theorem imp_eq (p q : Prop) : (p → q) = (¬ p ∨ q) := by
  by_cases p <;> by_cases q <;> simp [*]

-- And
@[grind_norm↓] theorem not_and (p q : Prop) : (¬(p ∧ q)) = (¬p ∨ ¬q) := by
  by_cases p <;> by_cases q <;> simp [*]
attribute [grind_norm] and_true true_and and_false false_and and_assoc

-- Or
attribute [grind_norm↓] not_or
attribute [grind_norm] or_true true_or or_false false_or or_assoc

-- ite
attribute [grind_norm] ite_true ite_false
@[grind_norm↓] theorem not_ite {_ : Decidable p} (q r : Prop) : (¬ite p q r) = ite p (¬q) (¬r) := by
  by_cases p <;> simp [*]

-- Forall
@[grind_norm↓] theorem not_forall (p : α → Prop) : (¬∀ x, p x) = ∃ x, ¬p x := by simp
attribute [grind_norm] forall_and

-- Exists
@[grind_norm↓] theorem not_exists (p : α → Prop) : (¬∃ x, p x) = ∀ x, ¬p x := by simp
attribute [grind_norm] exists_const exists_or

-- Bool cond
@[grind_norm] theorem cond_eq_ite (c : Bool) (a b : α) : cond c a b = ite c a b := by
  cases c <;> simp [*]

-- Bool or
attribute [grind_norm]
  Bool.or_false Bool.or_true Bool.false_or Bool.true_or Bool.or_eq_true Bool.or_assoc

-- Bool and
attribute [grind_norm]
  Bool.and_false Bool.and_true Bool.false_and Bool.true_and Bool.and_eq_true Bool.and_assoc

-- Bool not
attribute [grind_norm]
  Bool.not_not

-- beq
attribute [grind_norm] beq_iff_eq

-- bne
attribute [grind_norm] bne_iff_ne

-- Bool not eq true/false
attribute [grind_norm] Bool.not_eq_true Bool.not_eq_false

-- decide
attribute [grind_norm] decide_eq_true_eq decide_not not_decide_eq_true

-- Nat LE
attribute [grind_norm] Nat.le_zero_eq

-- Nat/Int LT
@[grind_norm] theorem Nat.lt_eq (a b : Nat) : (a < b) = (a + 1 ≤ b) := by
  simp [Nat.lt, LT.lt]

@[grind_norm] theorem Int.lt_eq (a b : Int) : (a < b) = (a + 1 ≤ b) := by
  simp [Int.lt, LT.lt]

-- GT GE
attribute [grind_norm] GT.gt GE.ge

end Lean.Grind
