/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import all Init.Grind.ToInt

public section

namespace Lean.Grind.ToInt

/-! Wrap -/

theorem of_eq_wrap_co_0 (i : IntInterval) (hi : Int) (h : i == .co 0 hi) {a b : Int} : a = i.wrap b → a = b % hi := by
  revert h
  cases i <;> simp
  intro h₁ h₂; subst h₁ h₂; simp

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

theorem of_not_le {α i} [ToInt α i] [_root_.LE α] [ToInt.LE α i] {a b : α} {a' b' : Int}
    (h₁ : toInt a = a') (h₂ : toInt b = b') : ¬ (a ≤ b) → b' + 1 ≤ a' := by
  intro h; have h' := ToInt.LE.le_iff a b
  simp [h, h₁, h₂] at h'; exact h'

theorem of_lt {α i} [ToInt α i] [_root_.LT α] [ToInt.LT α i] {a b : α} {a' b' : Int}
    (h₁ : toInt a = a') (h₂ : toInt b = b') : a < b → a' + 1 ≤ b' := by
  intro h; replace h := ToInt.LT.lt_iff _ _ |>.mp h
  rw [h₁, h₂] at h; assumption

theorem of_not_lt {α i} [ToInt α i] [_root_.LT α] [ToInt.LT α i] {a b : α} {a' b' : Int}
    (h₁ : toInt a = a') (h₂ : toInt b = b') : ¬ (a < b) → b' ≤ a' := by
  intro h; have h' := ToInt.LT.lt_iff a b
  simp [h, h₁, h₂] at h'; assumption

/-! Addition -/

theorem add_congr {α i} [ToInt α i] [_root_.Add α] [ToInt.Add α i] {a b : α} {a' b' : Int}
    (h₁ : toInt a = a') (h₂ : toInt b = b') : toInt (a + b) = i.wrap (a' + b') := by
  rw [ToInt.Add.toInt_add, h₁, h₂]

theorem add_congr.ww {α i} [ToInt α i] [_root_.Add α] [ToInt.Add α i] (h : i.isFinite) {a b : α} {a' b' : Int}
    (h₁ : toInt a = i.wrap a') (h₂ : toInt b = i.wrap b') : toInt (a + b) = i.wrap (a' + b') := by
  rw [add_congr h₁ h₂, ← i.wrap_add h]

theorem add_congr.wr {α i} [ToInt α i] [_root_.Add α] [ToInt.Add α i] (h : i.isFinite) (h' : i.nonEmpty) {a b : α} {a' b' : Int}
    (h₁ : toInt a = a') (h₂ : toInt b = i.wrap b') : toInt (a + b) = i.wrap (a' + b') := by
  have := i.wrap_eq_self_iff h' _ |>.mpr (ToInt.toInt_mem a)
  rw [h₁] at this; rw [← this] at h₁; apply add_congr.ww h h₁ h₂

theorem add_congr.wl {α i} [ToInt α i] [_root_.Add α] [ToInt.Add α i] (h : i.isFinite) (h' : i.nonEmpty) {a b : α} {a' b' : Int}
    (h₁ : toInt a = i.wrap a') (h₂ : toInt b = b') : toInt (a + b) = i.wrap (a' + b') := by
  have := i.wrap_eq_self_iff h' _ |>.mpr (ToInt.toInt_mem b)
  rw [h₂] at this; rw [← this] at h₂; apply add_congr.ww h h₁ h₂

/-! Multiplication -/

theorem mul_congr {α i} [ToInt α i] [_root_.Mul α] [ToInt.Mul α i] {a b : α} {a' b' : Int}
    (h₁ : toInt a = a') (h₂ : toInt b = b') : toInt (a * b) = i.wrap (a' * b') := by
  rw [ToInt.Mul.toInt_mul, h₁, h₂]

theorem mul_congr.ww {α i} [ToInt α i] [_root_.Mul α] [ToInt.Mul α i] (h : i.isFinite) {a b : α} {a' b' : Int}
    (h₁ : toInt a = i.wrap a') (h₂ : toInt b = i.wrap b') : toInt (a * b) = i.wrap (a' * b') := by
  rw [ToInt.Mul.toInt_mul, h₁, h₂, ← i.wrap_mul]; apply h

theorem mul_congr.wr {α i} [ToInt α i] [_root_.Mul α] [ToInt.Mul α i] (h : i.isFinite) (h' : i.nonEmpty) {a b : α} {a' b' : Int}
    (h₁ : toInt a = a') (h₂ : toInt b = i.wrap b') : toInt (a * b) = i.wrap (a' * b') := by
  have := i.wrap_eq_self_iff h' _ |>.mpr (ToInt.toInt_mem a)
  rw [h₁] at this; rw [← this] at h₁; apply mul_congr.ww h h₁ h₂

theorem mul_congr.wl {α i} [ToInt α i] [_root_.Mul α] [ToInt.Mul α i] (h : i.isFinite) (h' : i.nonEmpty) {a b : α} {a' b' : Int}
    (h₁ : toInt a = i.wrap a') (h₂ : toInt b = b') : toInt (a * b) = i.wrap (a' * b') := by
  have := i.wrap_eq_self_iff h' _ |>.mpr (ToInt.toInt_mem b)
  rw [h₂] at this; rw [← this] at h₂; apply mul_congr.ww h h₁ h₂

/-! Subtraction -/

theorem sub_congr {α i} [ToInt α i] [_root_.Sub α] [ToInt.Sub α i] {a b : α} {a' b' : Int}
    (h₁ : toInt a = a') (h₂ : toInt b = b') : toInt (a - b) = i.wrap (a' - b') := by
  rw [ToInt.Sub.toInt_sub, h₁, h₂]

/-! Negation -/

theorem neg_congr {α i} [ToInt α i] [_root_.Neg α] [ToInt.Neg α i] {a : α} {a' : Int}
    (h₁ : toInt a = a') : toInt (- a) = i.wrap (- a') := by
  rw [ToInt.Neg.toInt_neg, h₁]

/-! Power -/

theorem pow_congr {α i} [ToInt α i] [HPow α Nat α] [ToInt.Pow α i] {a : α} (k : Nat) (a' : Int)
    (h₁ : toInt a = a') : toInt (a ^ k) = i.wrap (a' ^ k) := by
  rw [ToInt.Pow.toInt_pow, h₁]

/-! Division -/

theorem div_congr {α i} [ToInt α i] [_root_.Div α] [ToInt.Div α i] {a b : α} {a' b' : Int}
    (h₁ : toInt a = a') (h₂ : toInt b = b') : toInt (a / b) = a' / b' := by
  rw [ToInt.Div.toInt_div, h₁, h₂]

/-! Modulo -/

theorem mod_congr {α i} [ToInt α i] [_root_.Mod α] [ToInt.Mod α i] {a b : α} {a' b' : Int}
    (h₁ : toInt a = a') (h₂ : toInt b = b') : toInt (a % b) = a' % b' := by
  rw [ToInt.Mod.toInt_mod, h₁, h₂]

/-! OfNat -/

theorem ofNat_eq {α i} [ToInt α i] [∀ n, _root_.OfNat α n] [ToInt.OfNat α i] (n : Nat)
    : toInt (OfNat.ofNat (α := α) n) = i.wrap n := by
  apply ToInt.OfNat.toInt_ofNat

/-! Zero -/

theorem zero_eq {α i} [ToInt α i] [_root_.Zero α] [ToInt.Zero α i] : toInt (0 : α) = 0 := by
  apply ToInt.Zero.toInt_zero

/-! Lower and upper bounds -/

theorem ge_lower {α i} [ToInt α i] (lo : Int) (h : i.lo? == some lo) (a : α) : -1 * toInt a + lo ≤ 0 := by
  have h' := ToInt.toInt_mem a
  revert h h'; cases i <;> simp [IntInterval.lo?] <;> intro h <;> subst h <;> intros <;> omega

theorem ge_lower0 {α i} [ToInt α i] (h : i.lo? == some 0) (a : α) : -1 * toInt a ≤ 0 := by
  have h' := ToInt.toInt_mem a
  revert h h'; cases i <;> simp [IntInterval.lo?] <;> intro h <;> subst h <;> intros <;> omega

theorem le_upper {α i} [ToInt α i] (hi' : Int) (h : i.hi? == some (-hi' + 1)) (a : α) : toInt a + hi' ≤ 0 := by
  have h' := ToInt.toInt_mem a
  revert h h'; cases i <;> simp [IntInterval.hi?] <;> intro h <;> subst h <;> intros <;> omega

end Lean.Grind.ToInt
