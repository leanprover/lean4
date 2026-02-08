/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Grind.Ordered.Ring
import Init.Data.Int.LemmasAux
import Init.Ext
import Init.Grind.Ordered.Order
import Init.Omega
public section
namespace Lean.Grind.Order

attribute [local instance] Ring.intCast

/-!
Helper theorems to assert constraints
-/
theorem eq_mp {p q : Prop} (h₁ : p = q) (h₂ : p) : q := by
  subst p; simp [*]

theorem eq_mp_not {p q : Prop} (h₁ : p = q) (h₂ : ¬ p) : ¬ q := by
  subst p; simp [*]

theorem eq_trans_true {p q : Prop} (h₁ : p = q) (h₂ : q = True) : p = True := by
  subst p; simp [*]

theorem eq_trans_false {p q : Prop} (h₁ : p = q) (h₂ : q = False) : p = False := by
  subst p; simp [*]

theorem eq_trans_true' {p q : Prop} (h₁ : p = q) (h₂ : p = True) : q = True := by
  subst p; simp [*]

theorem eq_trans_false' {p q : Prop} (h₁ : p = q) (h₂ : p = False) : q = False := by
  subst p; simp [*]

theorem le_of_eq_1 {α} [LE α] [Std.IsPreorder α]
    {a b : α} : a = b → a ≤ b := by
  intro h; subst a; apply Std.IsPreorder.le_refl

theorem le_of_eq_2 {α} [LE α] [Std.IsPreorder α]
    {a b : α} : a = b → b ≤ a := by
  intro h; subst a; apply Std.IsPreorder.le_refl

/-
**Note**: `le_of_eq_1_k` and `le_of_eq_2_k` contain unnecessary instances, but the extra arguments
simplify the proof generation in `grind order` (fewer cases).
-/
theorem le_of_eq_1_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    {a b : α} : a = b → a ≤ b + Int.cast (R := α) 0 := by
  rw [Ring.intCast_zero, Semiring.add_zero]
  intro h; subst a; apply Std.IsPreorder.le_refl

theorem le_of_eq_2_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    {a b : α} : a = b → b ≤ a + Int.cast (R := α) 0 := by
  rw [Ring.intCast_zero, Semiring.add_zero]
  intro h; subst a; apply Std.IsPreorder.le_refl

theorem le_of_offset_eq_1_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    {a b : α} {k : Int} : a = b + k → a ≤ b + k := by
  intro h; subst a; apply Std.IsPreorder.le_refl

theorem le_of_offset_eq_2_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    {a b : α} {k : Int} : a = b + k → b ≤ a + (-k : Int) := by
  intro h; subst a
  rw [Ring.intCast_neg, Semiring.add_assoc, Semiring.add_comm (α := α) k, Ring.neg_add_cancel, Semiring.add_zero]
  apply Std.IsPreorder.le_refl

theorem nat_eq (a b : Nat) (x y : Int) : NatCast.natCast a = x → NatCast.natCast b = y → x = y → a = b := by
  intro _ _; subst x y; intro h
  exact Int.natCast_inj.mp h

theorem of_nat_eq (a b : Nat) (x y : Int) : NatCast.natCast a = x → NatCast.natCast b = y → a = b → x = y := by
  intro _ _; subst x y; intro; simp [*]

theorem le_of_not_le {α} [LE α] [Std.IsLinearPreorder α]
    {a b : α} : ¬ a ≤ b → b ≤ a := by
  intro h
  have := Std.IsLinearPreorder.le_total a b
  cases this; contradiction; assumption

theorem lt_of_not_le {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearPreorder α]
    {a b : α} : ¬ a ≤ b → b < a := by
  intro h
  rw [Std.LawfulOrderLT.lt_iff]
  have := Std.IsLinearPreorder.le_total a b
  cases this; contradiction; simp [*]

theorem le_of_not_lt {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearPreorder α]
    {a b : α} : ¬ a < b → b ≤ a := by
  rw [Std.LawfulOrderLT.lt_iff]
  open Classical in
  rw [Classical.not_and_iff_not_or_not, Classical.not_not]
  intro h; cases h
  next =>
    have := Std.IsLinearPreorder.le_total a b
    cases this; contradiction; assumption
  next => assumption

theorem le_of_not_lt_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearPreorder α] [Ring α] [OrderedRing α]
    {a b : α} {k k' : Int} : k'.beq' (-k) → ¬ a < b + k → b ≤ a + k'  := by
  simp; intro _ h; subst k'
  replace h := le_of_not_lt h
  replace h := OrderedAdd.add_le_left h (-k)
  rw [Semiring.add_assoc, AddCommGroup.add_neg_cancel, Semiring.add_zero] at h
  rw [Ring.intCast_neg]
  assumption

theorem lt_of_not_le_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearPreorder α] [Ring α] [OrderedRing α]
    {a b : α} {k k' : Int} : k'.beq' (-k) → ¬ a ≤ b + k → b < a + k'  := by
  simp; intro _ h; subst k'
  replace h := lt_of_not_le h
  replace h := OrderedAdd.add_lt_left h (-k)
  rw [Semiring.add_assoc, AddCommGroup.add_neg_cancel, Semiring.add_zero] at h
  rw [Ring.intCast_neg]
  assumption

theorem int_lt {x y k k' : Int} : k'.beq' (k-1) → x < y + k → x ≤ y + k' := by
  simp; intro; subst k'; omega

/-!
Helper theorem for equality propagation
-/

theorem eq_of_le_of_le {α} [LE α] [Std.IsPartialOrder α] {a b : α} : a ≤ b → b ≤ a → a = b :=
  Std.IsPartialOrder.le_antisymm _ _

theorem eq_of_le_of_le_0 {α} [LE α] [Std.IsPartialOrder α] [Ring α]
    {a b : α} : a ≤ b + Int.cast (R := α) 0 → b ≤ a + Int.cast (R := α) 0 → a = b := by
  simp [Ring.intCast_zero, Semiring.add_zero]
  apply Std.IsPartialOrder.le_antisymm

/-!
Transitivity
-/

theorem le_trans {α} [LE α] [Std.IsPreorder α] {a b c : α} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
  Std.IsPreorder.le_trans _ _ _ h₁ h₂

theorem lt_trans {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] {a b c : α} (h₁ : a < b) (h₂ : b < c) : a < c :=
  Preorder.lt_trans h₁ h₂

theorem le_lt_trans {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] {a b c : α} (h₁ : a ≤ b) (h₂ : b < c) : a < c :=
  Preorder.lt_of_le_of_lt h₁ h₂

theorem lt_le_trans {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] {a b c : α} (h₁ : a < b) (h₂ : b ≤ c) : a < c :=
  Preorder.lt_of_lt_of_le h₁ h₂

theorem lt_unsat {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] (a : α) : a < a → False :=
  Preorder.lt_irrefl a

/-!
Transitivity with offsets
-/

theorem le_trans_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    {a b c : α} {k₁ k₂ : Int} (k : Int) (h₁ : a ≤ b + k₁) (h₂ : b ≤ c + k₂) : k == k₂ + k₁ → a ≤ c + k := by
  intro h; simp at h; subst k
  replace h₂ := OrderedAdd.add_le_left_iff (M := α) k₁ |>.mp h₂
  have := le_trans h₁ h₂
  simp [Ring.intCast_add, ← Semiring.add_assoc, this]

theorem lt_trans_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    {a b c : α} {k₁ k₂ : Int} (k : Int) (h₁ : a < b + k₁) (h₂ : b < c + k₂) : k == k₂ + k₁ → a < c + k := by
  intro h; simp at h; subst k
  replace h₂ := OrderedAdd.add_lt_left_iff (M := α) k₁ |>.mp h₂
  have := lt_trans h₁ h₂
  simp [Ring.intCast_add, ← Semiring.add_assoc, this]

theorem le_lt_trans_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    {a b c : α} {k₁ k₂ : Int} (k : Int) (h₁ : a ≤ b + k₁) (h₂ : b < c + k₂) : k == k₂ + k₁ → a < c + k := by
  intro h; simp at h; subst k
  replace h₂ := OrderedAdd.add_lt_left_iff (M := α) k₁ |>.mp h₂
  have := le_lt_trans h₁ h₂
  simp [Ring.intCast_add, ← Semiring.add_assoc, this]

theorem lt_le_trans_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    {a b c : α} {k₁ k₂ : Int} (k : Int) (h₁ : a < b + k₁) (h₂ : b ≤ c + k₂) : k == k₂ + k₁ → a < c + k := by
  intro h; simp at h; subst k
  replace h₂ := OrderedAdd.add_le_left_iff (M := α) k₁ |>.mp h₂
  have := lt_le_trans h₁ h₂
  simp [Ring.intCast_add, ← Semiring.add_assoc, this]

/-!
Unsat detection
-/

theorem le_unsat_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    {a : α} {k : Int} : k.blt' 0 → a ≤ a + k → False := by
  simp; intro h₁ h₂
  replace h₂ := OrderedAdd.add_le_left_iff (-a) |>.mp h₂
  rw [AddCommGroup.add_neg_cancel, Semiring.add_assoc, Semiring.add_comm _ (-a)] at h₂
  rw [← Semiring.add_assoc, AddCommGroup.add_neg_cancel, Semiring.add_comm, Semiring.add_zero] at h₂
  rw [← Ring.intCast_zero] at h₂
  replace h₂ := OrderedRing.le_of_intCast_le_intCast _ _ h₂
  omega

theorem lt_unsat_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    {a : α} {k : Int} : k.ble' 0 → a < a + k → False := by
  simp; intro h₁ h₂
  replace h₂ := OrderedAdd.add_lt_left_iff (-a) |>.mp h₂
  rw [AddCommGroup.add_neg_cancel, Semiring.add_assoc, Semiring.add_comm _ (-a)] at h₂
  rw [← Semiring.add_assoc, AddCommGroup.add_neg_cancel, Semiring.add_comm, Semiring.add_zero] at h₂
  rw [← Ring.intCast_zero] at h₂
  replace h₂ := OrderedRing.lt_of_intCast_lt_intCast _ _ h₂
  omega

/-!
Helper theorems
-/

private theorem add_lt_add_of_le_of_lt {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    {a b c d : α} (hab : a ≤ b) (hcd : c < d) : a + c < b + d :=
  lt_le_trans (OrderedAdd.add_lt_right a hcd) (OrderedAdd.add_le_left hab d)

private theorem add_lt_add_of_lt_of_le {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    {a b c d : α} (hab : a < b) (hcd : c ≤ d) : a + c < b + d :=
  le_lt_trans (OrderedAdd.add_le_right a hcd) (OrderedAdd.add_lt_left hab d)

/-! Theorems for propagating constraints to `True` -/

theorem le_eq_true_of_lt {α} [LE α] [LT α] [Std.LawfulOrderLT α]
    {a b : α} : a < b → (a ≤ b) = True := by
  simp; intro h
  exact Std.le_of_lt h

theorem le_eq_true {α} [LE α] [Std.IsPreorder α]
    {a : α} : (a ≤ a) = True := by
  simp

theorem le_eq_true_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    {a : α} {k : Int} : (0 : Int).ble' k → (a ≤ a + k) = True := by
  simp
  intro h
  replace h := OrderedRing.nonneg_intCast_of_nonneg (R := α) _ h
  have h₁ := Std.le_refl a
  replace h₁ := OrderedAdd.add_le_add h₁ h
  simp [Semiring.add_zero] at h₁
  assumption

theorem lt_eq_true_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    {a : α} {k : Int} : (0 : Int).blt' k → (a < a + k) = True := by
  simp
  intro h
  replace h := OrderedRing.pos_intCast_of_pos (R := α) _ h
  have h₁ := Std.le_refl a
  replace h₁ := add_lt_add_of_le_of_lt h₁ h
  simp [Semiring.add_zero] at h₁
  assumption

theorem le_eq_true_of_le_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    {a b : α} {k₁ k₂ : Int} : k₁.ble' k₂ → a ≤ b + k₁ → (a ≤ b + k₂) = True := by
  simp; intro h₁ h₂
  replace h₁ : 0 ≤ k₂ - k₁ := by omega
  replace h₁ := OrderedRing.nonneg_intCast_of_nonneg (R := α) _ h₁
  replace h₁ := OrderedAdd.add_le_add h₂ h₁
  rw [Semiring.add_zero, Semiring.add_assoc, Int.sub_eq_add_neg, Int.add_comm] at h₁
  rw [Ring.intCast_add, Ring.intCast_neg, ← Semiring.add_assoc (k₁ : α)] at h₁
  rw [AddCommGroup.add_neg_cancel, Semiring.add_comm 0, Semiring.add_zero] at h₁
  assumption

theorem le_eq_true_of_lt_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    {a b : α} {k₁ k₂ : Int} : k₁.ble' k₂ → a < b + k₁ → (a ≤ b + k₂) = True := by
  intro h₁ h₂
  replace h₂ := Std.le_of_lt h₂
  apply le_eq_true_of_le_k <;> assumption

theorem lt_eq_true_of_lt_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    {a b : α} {k₁ k₂ : Int} : k₁.ble' k₂ → a < b + k₁ → (a < b + k₂) = True := by
  simp; intro h₁ h₂
  replace h₁ : 0 ≤ k₂ - k₁ := by omega
  replace h₁ := OrderedRing.nonneg_intCast_of_nonneg (R := α) _ h₁
  replace h₁ := add_lt_add_of_le_of_lt h₁ h₂
  rw [Semiring.add_comm, Semiring.add_zero, Semiring.add_comm, Semiring.add_assoc, Int.sub_eq_add_neg, Int.add_comm] at h₁
  rw [Ring.intCast_add, Ring.intCast_neg, ← Semiring.add_assoc (k₁ : α)] at h₁
  rw [AddCommGroup.add_neg_cancel, Semiring.add_comm 0, Semiring.add_zero] at h₁
  assumption

theorem lt_eq_true_of_le_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    {a b : α} {k₁ k₂ : Int} : k₁.blt' k₂ → a ≤ b + k₁ → (a < b + k₂) = True := by
  simp; intro h₁ h₂
  replace h₁ : 0 < k₂ - k₁ := by omega
  replace h₁ := OrderedRing.pos_intCast_of_pos (R := α) _ h₁
  replace h₁ := add_lt_add_of_le_of_lt h₂ h₁
  rw [Semiring.add_zero, Semiring.add_assoc, Int.sub_eq_add_neg, Int.add_comm] at h₁
  rw [Ring.intCast_add, Ring.intCast_neg, ← Semiring.add_assoc (k₁ : α)] at h₁
  rw [AddCommGroup.add_neg_cancel, Semiring.add_comm 0, Semiring.add_zero] at h₁
  assumption

/-! Theorems for propagating constraints to `False` -/

theorem lt_eq_false {α} [LE α] [LT α] [Std.LawfulOrderLT α]
    {a : α} : (a < a) = False := by
  simp; intro h
  have := Preorder.lt_irrefl a
  contradiction

theorem le_eq_false_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    {a : α} {k : Int} : k.blt' 0 → (a ≤ a + k) = False := by
  simp
  intro h
  replace h := OrderedRing.neg_intCast_of_neg (R := α) _ h
  have h₁ := Std.le_refl a
  replace h₁ := add_lt_add_of_le_of_lt h₁ h
  simp [Semiring.add_zero] at h₁
  intro h
  have := Std.lt_of_lt_of_le h₁ h
  have := Preorder.lt_irrefl (a + k)
  contradiction

theorem lt_eq_false_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    {a : α} {k : Int} : k.ble' 0 → (a < a + k) = False := by
  simp
  intro h
  replace h := OrderedRing.nonpos_intCast_of_nonpos (R := α) _ h
  have h₁ := Std.le_refl a
  replace h₁ := OrderedAdd.add_le_add h₁ h
  simp [Semiring.add_zero] at h₁
  intro h
  have := Std.lt_of_le_of_lt h₁ h
  have := Preorder.lt_irrefl (a + k)
  contradiction

theorem le_eq_false_of_lt {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α]
    {a b : α} : a < b → (b ≤ a) = False := by
  simp; intro h₁ h₂
  have := lt_le_trans h₁ h₂
  have := Preorder.lt_irrefl a
  contradiction

theorem lt_eq_false_of_lt {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α]
    {a b : α} : a < b → (b < a) = False := by
  simp; intro h₁ h₂
  have := lt_trans h₁ h₂
  have := Preorder.lt_irrefl a
  contradiction

theorem lt_eq_false_of_le {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α]
    {a b : α} : a ≤ b → (b < a) = False := by
  simp; intro h₁ h₂
  have := le_lt_trans h₁ h₂
  have := Preorder.lt_irrefl a
  contradiction

theorem le_eq_false_of_le_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    {a b : α} {k₁ k₂ : Int} : (k₂ + k₁).blt' 0 → a ≤ b + k₁ → (b ≤ a + k₂) = False := by
  intro h₁; simp; intro h₂ h₃
  have h := le_trans_k (k₂ + k₁) h₂ h₃
  simp at h
  apply le_unsat_k h₁ h

theorem lt_eq_false_of_le_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    (a b : α) (k₁ k₂ : Int) : (k₂ + k₁).ble' 0 → a ≤ b + k₁ → (b < a + k₂) = False := by
  intro h₁; simp; intro h₂ h₃
  have h := le_lt_trans_k (k₂ + k₁) h₂ h₃
  simp at h
  apply lt_unsat_k h₁ h

theorem lt_eq_false_of_lt_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    (a b : α) (k₁ k₂ : Int) : (k₂ + k₁).ble' 0 → a < b + k₁ → (b < a + k₂) = False := by
  intro h₁; simp; intro h₂ h₃
  have h := lt_trans_k (k₂ + k₁) h₂ h₃
  simp at h
  apply lt_unsat_k h₁ h

theorem le_eq_false_of_lt_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    (a b : α) (k₁ k₂ : Int) : (k₂ + k₁).ble' 0 → a < b + k₁ → (b ≤ a + k₂) = False := by
  intro h₁; simp; intro h₂ h₃
  have h := lt_le_trans_k (k₂ + k₁) h₂ h₃
  simp at h
  apply lt_unsat_k h₁ h

end Lean.Grind.Order
