/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
import Init.Grind.ToInt

namespace Lean.Grind.ToInt

/-! Asserted propositions -/

theorem of_eq {α i} [ToInt α i] {a b : α} {a' b' : Int}
    (h₁ : toInt a = a') (h₂ : toInt b = b') : a = b → a' = b' := by
  intro h; replace h := congrArg toInt h
  rw [h₁, h₂] at h; assumption

theorem of_diseq {α i} [ToInt α i] {a b : α} {a' b' : Int}
    (h₁ : toInt a = a') (h₂ : toInt b = b') : a ≠ b → a' ≠ b' := by
  intro hne h; rw [← h₁, ← h₂] at h
  replace h := ToInt.toInt_inj _ _ h; contradiction

theorem of_le {α i} [ToInt α i] [_root_.LE α] [ToInt.LE α i] {a b : α} {a' b' : Int}
    (h₁ : toInt a = a') (h₂ : toInt b = b') : a ≤ b → a' ≤ b' := by
  intro h; replace h := ToInt.LE.le_iff _ _ |>.mp h
  rw [h₁, h₂] at h; assumption

theorem of_not_le_norm {α i} [ToInt α i] [_root_.LE α] [ToInt.LE α i] {a b : α} {a' b' : Int}
    (h₁ : toInt a = a') (h₂ : toInt b = b') : ¬ (a ≤ b) → b' + 1 ≤ a' := by
  intro h; have h' := ToInt.LE.le_iff a b
  simp [h, h₁, h₂] at h'; exact h'

theorem of_lt_norm {α i} [ToInt α i] [_root_.LT α] [ToInt.LT α i] {a b : α} {a' b' : Int}
    (h₁ : toInt a = a') (h₂ : toInt b = b') : a < b → a' + 1 ≤ b' := by
  intro h; replace h := ToInt.LT.lt_iff _ _ |>.mp h
  rw [h₁, h₂] at h; assumption

theorem of_not_lt_norm {α i} [ToInt α i] [_root_.LT α] [ToInt.LT α i] {a b : α} {a' b' : Int}
    (h₁ : toInt a = a') (h₂ : toInt b = b') : ¬ (a < b) → b' ≤ a' := by
  intro h; have h' := ToInt.LT.lt_iff a b
  simp [h, h₁, h₂] at h'; assumption

/-! Addition -/

theorem add_congr {α i} [ToInt α i] [_root_.Add α] [ToInt.Add α i] {a b : α} {a' b' : Int}
    (h₁ : toInt a = a') (h₂ : toInt b = b') : toInt (a + b) = i.wrap (a' + b') := by
  rw [ToInt.Add.toInt_add, h₁, h₂]

theorem add_congr_ww {α i} [ToInt α i] [_root_.Add α] [ToInt.Add α i] {a b : α} {a' b' : Int}
    (h : i.isFinite) (h₁ : toInt a = i.wrap a') (h₂ : toInt b = i.wrap b') : toInt (a + b) = i.wrap (a' + b') := by
  rw [add_congr h₁ h₂, ← i.wrap_add h]

theorem add_congr_wr {α i} [ToInt α i] [_root_.Add α] [ToInt.Add α i] {a b : α} {a' b' : Int}
    (h : i.isFinite) (h' : i.nonEmpty) (h₁ : toInt a = a') (h₂ : toInt b = i.wrap b') : toInt (a + b) = i.wrap (a' + b') := by
  have := i.wrap_eq_self_iff h' _ |>.mpr (ToInt.toInt_mem a)
  rw [h₁] at this; rw [← this] at h₁; apply add_congr_ww h h₁ h₂

theorem add_congr_wl {α i} [ToInt α i] [_root_.Add α] [ToInt.Add α i] {a b : α} {a' b' : Int}
    (h : i.isFinite) (h' : i.nonEmpty) (h₁ : toInt a = i.wrap a') (h₂ : toInt b = b') : toInt (a + b) = i.wrap (a' + b') := by
  have := i.wrap_eq_self_iff h' _ |>.mpr (ToInt.toInt_mem b)
  rw [h₂] at this; rw [← this] at h₂; apply add_congr_ww h h₁ h₂

/-! Multiplication -/

theorem mul_congr {α i} [ToInt α i] [_root_.Mul α] [ToInt.Mul α i] {a b : α} {a' b' : Int}
    (h₁ : toInt a = a') (h₂ : toInt b = b') : toInt (a * b) = i.wrap (a' * b') := by
  rw [ToInt.Mul.toInt_mul, h₁, h₂]

theorem mul_congr_ww {α i} [ToInt α i] [_root_.Mul α] [ToInt.Mul α i] {a b : α} {a' b' : Int}
    (h : i.isFinite) (h₁ : toInt a = i.wrap a') (h₂ : toInt b = i.wrap b') : toInt (a * b) = i.wrap (a' * b') := by
  rw [ToInt.Mul.toInt_mul, h₁, h₂, ← i.wrap_mul]; apply h

theorem mul_congr_wr {α i} [ToInt α i] [_root_.Mul α] [ToInt.Mul α i] {a b : α} {a' b' : Int}
    (h : i.isFinite) (h' : i.nonEmpty) (h₁ : toInt a = a') (h₂ : toInt b = i.wrap b') : toInt (a * b) = i.wrap (a' * b') := by
  have := i.wrap_eq_self_iff h' _ |>.mpr (ToInt.toInt_mem a)
  rw [h₁] at this; rw [← this] at h₁; apply mul_congr_ww h h₁ h₂

theorem mul_congr_wl {α i} [ToInt α i] [_root_.Mul α] [ToInt.Mul α i] {a b : α} {a' b' : Int}
    (h : i.isFinite) (h' : i.nonEmpty) (h₁ : toInt a = i.wrap a') (h₂ : toInt b = b') : toInt (a * b) = i.wrap (a' * b') := by
  have := i.wrap_eq_self_iff h' _ |>.mpr (ToInt.toInt_mem b)
  rw [h₂] at this; rw [← this] at h₂; apply mul_congr_ww h h₁ h₂

end Lean.Grind.ToInt
