/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Grind.Ordered.Ring
import Init.Grind.Ring
public section
namespace Lean.Grind.Order

/-!
Helper theorems to assert constraints
-/

theorem le_of_eq {α} [LE α] [Std.IsPreorder α]
    (a b : α) : a = b → a ≤ b := by
  intro h; subst a; apply Std.IsPreorder.le_refl

theorem le_of_not_le {α} [LE α] [Std.IsLinearPreorder α]
    (a b : α) : ¬ a ≤ b → b ≤ a := by
  intro h
  have := Std.IsLinearPreorder.le_total a b
  cases this; contradiction; assumption

theorem lt_of_not_le {α} [LE α] [LT α] [Std.IsLinearPreorder α] [Std.LawfulOrderLT α]
    (a b : α) : ¬ a ≤ b → b < a := by
  intro h
  rw [Std.LawfulOrderLT.lt_iff]
  have := Std.IsLinearPreorder.le_total a b
  cases this; contradiction; simp [*]

theorem le_of_not_lt {α} [LE α] [LT α] [Std.IsLinearPreorder α] [Std.LawfulOrderLT α]
    (a b : α) : ¬ a < b → b ≤ a := by
  rw [Std.LawfulOrderLT.lt_iff]
  open Classical in
  rw [Classical.not_and_iff_not_or_not, Classical.not_not]
  intro h; cases h
  next =>
    have := Std.IsLinearPreorder.le_total a b
    cases this; contradiction; assumption
  next => assumption

theorem int_lt (x y k : Int) : x < y + k → x ≤ y + (k-1) := by
  omega

/-!
Helper theorem for equality propagation
-/

theorem eq_of_le_of_le {α} [LE α] [Std.IsPartialOrder α] {a b : α} : a ≤ b → b ≤ a → a = b :=
  Std.IsPartialOrder.le_antisymm _ _

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

attribute [local instance] Ring.intCast

theorem le_trans_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    (a b c : α) (k₁ k₂ k : Int) (h₁ : a ≤ b + k₁) (h₂ : b ≤ c + k₂) : k == k₂ + k₁ → a ≤ c + k := by
  intro h; simp at h; subst k
  replace h₂ := OrderedAdd.add_le_left_iff (M := α) k₁ |>.mp h₂
  have := le_trans h₁ h₂
  simp [Ring.intCast_add, ← Semiring.add_assoc, this]

theorem lt_trans_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    (a b c : α) (k₁ k₂ k : Int) (h₁ : a < b + k₁) (h₂ : b < c + k₂) : k == k₂ + k₁ → a < c + k := by
  intro h; simp at h; subst k
  replace h₂ := OrderedAdd.add_lt_left_iff (M := α) k₁ |>.mp h₂
  have := lt_trans h₁ h₂
  simp [Ring.intCast_add, ← Semiring.add_assoc, this]

theorem le_lt_trans_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    (a b c : α) (k₁ k₂ k : Int) (h₁ : a ≤ b + k₁) (h₂ : b < c + k₂) : k == k₂ + k₁ → a < c + k := by
  intro h; simp at h; subst k
  replace h₂ := OrderedAdd.add_lt_left_iff (M := α) k₁ |>.mp h₂
  have := le_lt_trans h₁ h₂
  simp [Ring.intCast_add, ← Semiring.add_assoc, this]

theorem lt_le_trans_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    (a b c : α) (k₁ k₂ k : Int) (h₁ : a < b + k₁) (h₂ : b ≤ c + k₂) : k == k₂ + k₁ → a < c + k := by
  intro h; simp at h; subst k
  replace h₂ := OrderedAdd.add_le_left_iff (M := α) k₁ |>.mp h₂
  have := lt_le_trans h₁ h₂
  simp [Ring.intCast_add, ← Semiring.add_assoc, this]

/-!
Unsat detection
-/

theorem le_unsat_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    (a : α) (k : Int) : k.blt' 0 → a ≤ a + k → False := by
  simp; intro h₁ h₂
  replace h₂ := OrderedAdd.add_le_left_iff (-a) |>.mp h₂
  rw [AddCommGroup.add_neg_cancel, Semiring.add_assoc, Semiring.add_comm _ (-a)] at h₂
  rw [← Semiring.add_assoc, AddCommGroup.add_neg_cancel, Semiring.add_comm, Semiring.add_zero] at h₂
  rw [← Ring.intCast_zero] at h₂
  replace h₂ := OrderedRing.le_of_intCast_le_intCast _ _ h₂
  omega

theorem lt_unsat_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    (a : α) (k : Int) : k.ble' 0 → a < a + k → False := by
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
    (a b : α) : a < b → (a ≤ b) = True := by
  simp; intro h
  exact Std.le_of_lt h

theorem le_eq_true_of_le_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    (a b : α) (k₁ k₂ : Int) : k₁.ble' k₂ → a ≤ b + k₁ → (a ≤ b + k₂) = True := by
  simp; intro h₁ h₂
  replace h₁ : 0 ≤ k₂ - k₁ := by omega
  replace h₁ := OrderedRing.nonneg_intCast_of_nonneg (R := α) _ h₁
  replace h₁ := OrderedAdd.add_le_add h₂ h₁
  rw [Semiring.add_zero, Semiring.add_assoc, Int.sub_eq_add_neg, Int.add_comm] at h₁
  rw [Ring.intCast_add, Ring.intCast_neg, ← Semiring.add_assoc (k₁ : α)] at h₁
  rw [AddCommGroup.add_neg_cancel, Semiring.add_comm 0, Semiring.add_zero] at h₁
  assumption

theorem le_eq_true_of_lt_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    (a b : α) (k₁ k₂ : Int) : k₁.ble' k₂ → a < b + k₁ → (a ≤ b + k₂) = True := by
  intro h₁ h₂
  replace h₂ := Std.le_of_lt h₂
  apply le_eq_true_of_le_k <;> assumption

theorem lt_eq_true_of_lt_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    (a b : α) (k₁ k₂ : Int) : k₁.ble' k₂ → a < b + k₁ → (a < b + k₂) = True := by
  simp; intro h₁ h₂
  replace h₁ : 0 ≤ k₂ - k₁ := by omega
  replace h₁ := OrderedRing.nonneg_intCast_of_nonneg (R := α) _ h₁
  replace h₁ := add_lt_add_of_le_of_lt h₁ h₂
  rw [Semiring.add_comm, Semiring.add_zero, Semiring.add_comm, Semiring.add_assoc, Int.sub_eq_add_neg, Int.add_comm] at h₁
  rw [Ring.intCast_add, Ring.intCast_neg, ← Semiring.add_assoc (k₁ : α)] at h₁
  rw [AddCommGroup.add_neg_cancel, Semiring.add_comm 0, Semiring.add_zero] at h₁
  assumption

theorem lt_eq_true_of_le_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    (a b : α) (k₁ k₂ : Int) : k₁.blt' k₂ → a ≤ b + k₁ → (a < b + k₂) = True := by
  simp; intro h₁ h₂
  replace h₁ : 0 < k₂ - k₁ := by omega
  replace h₁ := OrderedRing.pos_intCast_of_pos (R := α) _ h₁
  replace h₁ := add_lt_add_of_le_of_lt h₂ h₁
  rw [Semiring.add_zero, Semiring.add_assoc, Int.sub_eq_add_neg, Int.add_comm] at h₁
  rw [Ring.intCast_add, Ring.intCast_neg, ← Semiring.add_assoc (k₁ : α)] at h₁
  rw [AddCommGroup.add_neg_cancel, Semiring.add_comm 0, Semiring.add_zero] at h₁
  assumption

/-! Theorems for propagating constraints to `False` -/

theorem le_eq_false_of_lt {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α]
    (a b : α) : a < b → (b ≤ a) = False := by
  simp; intro h₁ h₂
  have := lt_le_trans h₁ h₂
  have := Preorder.lt_irrefl a
  contradiction

theorem lt_eq_false_of_lt {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α]
    (a b : α) : a < b → (b < a) = False := by
  simp; intro h₁ h₂
  have := lt_trans h₁ h₂
  have := Preorder.lt_irrefl a
  contradiction

theorem lt_eq_false_of_le {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α]
    (a b : α) : a ≤ b → (b < a) = False := by
  simp; intro h₁ h₂
  have := le_lt_trans h₁ h₂
  have := Preorder.lt_irrefl a
  contradiction

theorem le_eq_false_of_le_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    (a b : α) (k₁ k₂ : Int) : (k₂ + k₁).blt' 0 → a ≤ b + k₁ → (b ≤ a + k₂) = False := by
  intro h₁; simp; intro h₂ h₃
  have h := le_trans_k _ _ _ _ _ (k₂ + k₁) h₂ h₃
  simp at h
  apply le_unsat_k _ _ h₁ h

theorem lt_eq_false_of_le_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    (a b : α) (k₁ k₂ : Int) : (k₂ + k₁).ble' 0 → a ≤ b + k₁ → (b < a + k₂) = False := by
  intro h₁; simp; intro h₂ h₃
  have h := le_lt_trans_k _ _ _ _ _ (k₂ + k₁) h₂ h₃
  simp at h
  apply lt_unsat_k _ _ h₁ h

theorem lt_eq_false_of_lt_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    (a b : α) (k₁ k₂ : Int) : (k₂ + k₁).ble' 0 → a < b + k₁ → (b < a + k₂) = False := by
  intro h₁; simp; intro h₂ h₃
  have h := lt_trans_k _ _ _ _ _ (k₂ + k₁) h₂ h₃
  simp at h
  apply lt_unsat_k _ _ h₁ h

theorem le_eq_false_of_lt_k {α} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    (a b : α) (k₁ k₂ : Int) : (k₂ + k₁).ble' 0 → a < b + k₁ → (b ≤ a + k₂) = False := by
  intro h₁; simp; intro h₂ h₃
  have h := lt_le_trans_k _ _ _ _ _ (k₂ + k₁) h₂ h₃
  simp at h
  apply lt_unsat_k _ _ h₁ h

end Lean.Grind.Order
