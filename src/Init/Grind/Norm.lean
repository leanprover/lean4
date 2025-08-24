/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.SimpLemmas
public import Init.PropLemmas
public import Init.Classical
public import Init.ByCases
public import Init.Data.Int.Linear
public import Init.Data.Int.Pow
public import Init.Grind.Ring.Field

public section

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

-- Unless `+splitImp` is used, `grind` will not be able to do much with this kind of implication.
-- Thus, this normalization step is enabled by default.
theorem forall_imp_eq_or {α} (p : α → Prop) (q : Prop) : ((∀ a, p a) → q) = ((∃ a, ¬ p a) ∨ q) := by
  rw [imp_eq]; simp

theorem true_imp_eq (p : Prop) : (True → p) = p := by simp
theorem false_imp_eq (p : Prop) : (False → p) = True := by simp
theorem imp_true_eq (p : Prop) : (p → True) = True := by simp
theorem imp_false_eq (p : Prop) : (p → False) = ¬p := by simp
theorem imp_self_eq (p : Prop) : (p → p) = True := by simp

theorem not_true : (¬True) = False := by simp
theorem not_false : (¬False) = True := by simp
theorem not_not (p : Prop) : (¬¬p) = p := by by_cases p <;> simp [*]
theorem not_and (p q : Prop) : (¬(p ∧ q)) = (¬p ∨ ¬q) := by by_cases p <;> by_cases q <;> simp [*]
theorem not_or (p q : Prop) : (¬(p ∨ q)) = (¬p ∧ ¬q) := by by_cases p <;> by_cases q <;> simp [*]
theorem not_ite {_ : Decidable p} (q r : Prop) : (¬ite p q r) = ite p (¬q) (¬r) := by by_cases p <;> simp [*]
theorem not_forall (p : α → Prop) : (¬∀ x, p x) = ∃ x, ¬p x := by simp
theorem not_exists (p : α → Prop) : (¬∃ x, p x) = ∀ x, ¬p x := by simp
theorem not_implies (p q : Prop) : (¬(p → q)) = (p ∧ ¬q) := by simp

theorem or_assoc (p q r : Prop) : ((p ∨ q) ∨ r) = (p ∨ (q ∨ r)) := by by_cases p <;> simp [*]
theorem or_swap12 (p q r : Prop) : (p ∨ q ∨ r) = (q ∨ p ∨ r) := by by_cases p <;> simp [*]
theorem or_swap13 (p q r : Prop) : (p ∨ q ∨ r) = (r ∨ q ∨ p) := by by_cases p <;> by_cases q <;> simp [*]

theorem ite_true_false {_ : Decidable p} : (ite p True False) = p := by
  by_cases p <;> simp

theorem ite_false_true {_ : Decidable p} : (ite p False True) = ¬p := by
  by_cases p <;> simp

theorem cond_eq_ite (c : Bool) (a b : α) : cond c a b = ite c a b := by
  cases c <;> simp [*]

theorem Nat.lt_eq (a b : Nat) : (a < b) = (a + 1 ≤ b) := by
  simp [Nat.lt, LT.lt]

theorem Int.lt_eq (a b : Int) : (a < b) = (a + 1 ≤ b) := by
  simp [Int.lt, LT.lt]

theorem beq_eq_decide_eq {_ : BEq α} [LawfulBEq α] [DecidableEq α] (a b : α) : (a == b) = (decide (a = b)) := by
  by_cases a = b
  next h => simp [h]
  next h => simp [beq_eq_false_iff_ne.mpr h, decide_eq_false h]

theorem bne_eq_decide_not_eq {_ : BEq α} [LawfulBEq α] [DecidableEq α] (a b : α) : (a != b) = (decide (¬ a = b)) := by
  by_cases a = b <;> simp [*]

theorem natCast_div (a b : Nat) : (NatCast.natCast (a / b) : Int) = (NatCast.natCast a) / (NatCast.natCast b) := rfl
theorem natCast_mod (a b : Nat) : (NatCast.natCast (a % b) : Int) = (NatCast.natCast a) % (NatCast.natCast b) := rfl
theorem natCast_add (a b : Nat) : (NatCast.natCast (a + b : Nat) : Int) = (NatCast.natCast a : Int) + (NatCast.natCast b : Int) := rfl
theorem natCast_mul (a b : Nat) : (NatCast.natCast (a * b : Nat) : Int) = (NatCast.natCast a : Int) * (NatCast.natCast b : Int) := rfl
theorem natCast_pow (a b : Nat) : (NatCast.natCast (a ^ b : Nat) : Int) = (NatCast.natCast a : Int) ^ b := by simp

theorem Nat.pow_one (a : Nat) : a ^ 1 = a := by
  simp

theorem Int.pow_one (a : Int) : a ^ 1 = a := by
  simp [Int.pow_succ]

theorem forall_true (p : True → Prop) : (∀ h : True, p h) = p True.intro :=
  propext <| Iff.intro (fun h => h True.intro) (fun h _ => h)

-- Helper theorem used by the simproc `simpBoolEq`
theorem flip_bool_eq (a b : Bool) : (a = b) = (b = a) := by
  rw [@Eq.comm _ a b]

-- Helper theorem used by the simproc `simpBoolEq`
theorem bool_eq_to_prop (a b : Bool) : (a = b) = ((a = true) = (b = true)) := by
  simp

theorem forall_or_forall {α : Sort u} {β : α → Sort v} (p : α → Prop) (q : (a : α) → β a → Prop)
    : (∀ a : α, p a ∨ ∀ b : β a, q a b) =
      (∀ (a : α) (b : β a), p a ∨ q a b) := by
  apply propext; constructor
  · intro h a b; cases h a <;> simp [*]
  · intro h a
    apply Classical.byContradiction
    intro h'; simp at h'; have ⟨h₁, b, h₂⟩ := h'
    replace h := h a b; simp [h₁, h₂] at h

theorem forall_forall_or {α : Sort u} {β : α → Sort v} (p : α → Prop) (q : (a : α) → β a → Prop)
    : (∀ a : α, (∀ b : β a, q a b) ∨ p a) =
      (∀ (a : α) (b : β a), q a b ∨ p a) := by
  apply propext; constructor
  · intro h a b; cases h a <;> simp [*]
  · intro h a
    apply Classical.byContradiction
    intro h'; simp at h'; have ⟨⟨b, h₁⟩, h₂⟩ := h'
    replace h := h a b; simp [h₁, h₂] at h

theorem forall_and {α} {p q : α → Prop} : (∀ x, p x ∧ q x) = ((∀ x, p x) ∧ (∀ x, q x)) := by
  apply propext; apply _root_.forall_and

theorem exists_const (α : Sort u) [i : Nonempty α] {b : Prop} : (∃ _ : α, b) = b := by
  apply propext; apply _root_.exists_const

theorem exists_or {α : Sort u} {p q : α → Prop} : (∃ x, p x ∨ q x) = ((∃ x, p x) ∨ ∃ x, q x) := by
  apply propext; apply _root_.exists_or

theorem exists_prop {a b : Prop} : (∃ _h : a, b) = (a ∧ b) := by
  apply propext; apply _root_.exists_prop

theorem exists_and_left {α : Sort u} {p : α → Prop} {b : Prop} : (∃ x, b ∧ p x) = (b ∧ (∃ x, p x)) := by
  apply propext; apply _root_.exists_and_left

theorem exists_and_right {α : Sort u} {p : α → Prop} {b : Prop} : (∃ x, p x ∧ b) = ((∃ x, p x) ∧ b) := by
  apply propext; apply _root_.exists_and_right

theorem zero_sub (a : Nat) : 0 - a = 0 := by
  simp

attribute [local instance] Semiring.natCast Ring.intCast
theorem smul_nat_eq_mul {α} [Semiring α] (n : Nat) (a : α) : n • a = NatCast.natCast n * a := by
  rw [Semiring.nsmul_eq_natCast_mul]

theorem smul_int_eq_mul {α} [Ring α] (i : Int) (a : α) : i • a = Int.cast i * a := by
  rw [Ring.zsmul_eq_intCast_mul]

-- Remark: for additional `grind` simprocs, check `Lean/Meta/Tactic/Grind`
init_grind_norm
  /- Pre theorems -/
  |
  /- Post theorems -/
  iff_eq heq_eq_eq
  -- And
  and_true true_and and_false false_and and_assoc
  -- ite
  ite_true_false ite_false_true
  -- Bool cond
  cond_eq_ite
  -- Bool or
  Bool.or_false Bool.or_true Bool.false_or Bool.true_or Bool.or_eq_true
  -- Bool and
  Bool.and_false Bool.and_true Bool.false_and Bool.true_and Bool.and_eq_true
  -- Bool not
  Bool.not_not
  -- beq
  beq_iff_eq beq_eq_decide_eq beq_self_eq_true
  -- bne
  bne_iff_ne bne_eq_decide_not_eq
  -- decide
  decide_eq_true_eq decide_not not_decide_eq_true
  -- Nat
  Nat.le_zero_eq Nat.lt_eq Nat.succ_eq_add_one
  Nat.add_eq Nat.sub_eq Nat.mul_eq Nat.zero_eq Nat.le_eq
  Nat.div_zero Nat.mod_zero Nat.div_one Nat.mod_one
  Nat.sub_sub Nat.pow_zero Nat.pow_one Nat.sub_self
  Nat.one_pow Nat.zero_sub
  -- Int
  Int.lt_eq
  Int.emod_neg Int.ediv_neg
  Int.ediv_zero Int.emod_zero
  Int.ediv_one Int.emod_one
  Int.negSucc_eq
  natCast_div natCast_mod
  natCast_add natCast_mul natCast_pow
  Int.one_pow
  Int.pow_zero Int.pow_one
  -- Int op folding
  Int.add_def Int.mul_def Int.ofNat_eq_coe
  Int.Linear.sub_fold Int.Linear.neg_fold
  -- Int divides
  Int.one_dvd Int.zero_dvd
  -- Function composition
  Function.const_apply Function.comp_apply Function.const_comp
  Function.comp_const Function.true_comp Function.false_comp
  -- Field
  Field.inv_zero Field.inv_inv Field.inv_one Field.inv_neg
  -- SMul normalizer
  smul_int_eq_mul smul_nat_eq_mul

end Lean.Grind
