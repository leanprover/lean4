/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.Grind.Ring.Basic
public import Init.Grind.Ordered.Module

public section

open Std
namespace Lean.Grind

/--
A ring which is also equipped with a preorder is considered a strict ordered ring if addition, negation,
and multiplication are compatible with the preorder, and `0 < 1`.
-/
class OrderedRing (R : Type u) [Semiring R] [LE R] [LT R] [IsPreorder R] extends OrderedAdd R where
  /-- In a strict ordered semiring, we have `0 < 1`. -/
  zero_lt_one : (0 : R) < 1
  /-- In a strict ordered semiring, we can multiply an inequality `a < b` on the left
  by a positive element `0 < c` to obtain `c * a < c * b`. -/
  mul_lt_mul_of_pos_left : ∀ {a b c : R}, a < b → 0 < c → c * a < c * b
  /-- In a strict ordered semiring, we can multiply an inequality `a < b` on the right
  by a positive element `0 < c` to obtain `a * c < b * c`. -/
  mul_lt_mul_of_pos_right : ∀ {a b c : R}, a < b → 0 < c → a * c < b * c

namespace OrderedRing

variable {R : Type u} [Ring R]

section Preorder

variable [LE R] [LT R] [LawfulOrderLT R] [IsPreorder R] [OrderedRing R]

theorem neg_one_lt_zero : (-1 : R) < 0 := by
  have h := zero_lt_one (R := R)
  have := OrderedAdd.add_lt_left h (-1)
  rw [AddCommMonoid.zero_add, AddCommGroup.add_neg_cancel] at this
  assumption

theorem ofNat_nonneg (x : Nat) : (OfNat.ofNat x : R) ≥ 0 := by
  induction x
  next => simp [OfNat.ofNat, Zero.zero]; apply le_refl
  next n ih =>
    have := OrderedRing.zero_lt_one (R := R)
    rw [Semiring.ofNat_succ]
    replace ih := OrderedAdd.add_le_left ih 1
    rw [AddCommMonoid.zero_add] at ih
    have := Preorder.lt_of_lt_of_le this ih
    exact Preorder.le_of_lt this

attribute [local instance] Semiring.natCast Ring.intCast

theorem le_of_natCast_le_natCast (a b : Nat) : (a : R) ≤ (b : R) → a ≤ b := by
  induction a generalizing b <;> cases b <;> simp
  next n ih =>
    simp [Semiring.natCast_succ, Semiring.natCast_zero]
    intro h
    have : (n:R) ≤ 0 := by
      have := OrderedRing.zero_lt_one (R := R)
      replace this := OrderedAdd.add_le_right (M := R) (n:R) (Std.le_of_lt this)
      rw [Semiring.add_zero] at this
      exact Std.IsPreorder.le_trans _ _ _ this h
    replace ih := ih 0
    simp [Semiring.natCast_zero] at ih
    replace ih := ih this
    subst n
    clear this
    have := OrderedRing.zero_lt_one (R := R)
    rw [Semiring.natCast_zero, Semiring.add_comm, Semiring.add_zero] at h
    replace this := Std.lt_of_lt_of_le this h
    have := Preorder.lt_irrefl (0:R)
    contradiction
  next ih m =>
    simp [Semiring.natCast_succ]
    intro h
    have := OrderedAdd.add_le_left_iff _ |>.mpr h
    exact ih _ this

theorem le_of_intCast_le_intCast (a b : Int) : (a : R) ≤ (b : R) → a ≤ b := by
  intro h
  replace h := OrderedAdd.sub_nonneg_iff.mpr h
  rw [← Ring.intCast_sub] at h
  suffices 0 ≤ b - a by omega
  revert h
  generalize b - a = x
  cases x <;> simp [Ring.intCast_natCast, Int.negSucc_eq, Ring.intCast_neg, Ring.intCast_add]
  intro h
  replace h := OrderedAdd.neg_nonneg_iff.mp h
  rw [Ring.intCast_one, ← Semiring.natCast_one, ← Semiring.natCast_add, ← Semiring.natCast_zero] at h
  replace h := le_of_natCast_le_natCast _ _ h
  omega

theorem lt_of_natCast_lt_natCast (a b : Nat) : (a : R) < (b : R) → a < b := by
  induction a generalizing b <;> cases b <;> simp
  next =>
    simp [Semiring.natCast_zero]
    exact Preorder.lt_irrefl (0:R)
  next n ih =>
    simp [Semiring.natCast_succ, Semiring.natCast_zero]
    intro h
    have : (n:R) < 0 := by
      have := OrderedRing.zero_lt_one (R := R)
      replace this := OrderedAdd.add_le_right (M := R) (n:R) (Std.le_of_lt this)
      rw [Semiring.add_zero] at this
      exact Std.lt_of_le_of_lt this h
    replace ih := ih 0
    simp [Semiring.natCast_zero] at ih
    exact ih this
  next ih m =>
    simp [Semiring.natCast_succ]
    intro h
    have := OrderedAdd.add_lt_left_iff _ |>.mpr h
    exact ih _ this

theorem lt_of_intCast_lt_intCast (a b : Int) : (a : R) < (b : R) → a < b := by
  intro h
  replace h := OrderedAdd.sub_pos_iff.mpr h
  rw [← Ring.intCast_sub] at h
  suffices 0 < b - a by omega
  revert h
  generalize b - a = x
  cases x <;> simp [Ring.intCast_natCast, Int.negSucc_eq, Ring.intCast_neg, Ring.intCast_add]
  next => intro h; rw [← Semiring.natCast_zero] at h; exact lt_of_natCast_lt_natCast _ _ h
  next =>
    intro h
    replace h := OrderedAdd.neg_pos_iff.mp h
    rw [Ring.intCast_one, ← Semiring.natCast_one, ← Semiring.natCast_add, ← Semiring.natCast_zero] at h
    replace h := lt_of_natCast_lt_natCast _ _ h
    omega

theorem natCast_le_natCast_of_le (a b : Nat) : a ≤ b → (a : R) ≤ (b : R) := by
  induction a generalizing b <;> cases b <;> simp
  next => simp [Semiring.natCast_zero, Std.IsPreorder.le_refl]
  next n =>
    have := ofNat_nonneg (R := R) n
    simp [Semiring.ofNat_eq_natCast] at this
    rw [Semiring.natCast_zero] at this
    simp [Semiring.natCast_zero, Semiring.natCast_add, Semiring.natCast_one]
    replace this := OrderedAdd.add_le_left_iff 1 |>.mp this
    rw [Semiring.add_comm, Semiring.add_zero] at this
    replace this := Std.lt_of_lt_of_le zero_lt_one this
    exact Std.le_of_lt this
  next n ih m =>
    intro h
    replace ih := ih _ h
    simp [Semiring.natCast_add, Semiring.natCast_one]
    exact OrderedAdd.add_le_left_iff _ |>.mp ih

theorem natCast_nonneg {a : Nat} : 0 ≤ (a : R) := by
  simpa [Semiring.natCast_zero] using natCast_le_natCast_of_le (R := R) _ _ (Nat.zero_le a)

theorem natCast_lt_natCast_of_lt (a b : Nat) : a < b → (a : R) < (b : R) := by
  induction a generalizing b <;> cases b <;> simp
  next n =>
    have := ofNat_nonneg (R := R) n
    simp [Semiring.ofNat_eq_natCast] at this
    rw [Semiring.natCast_zero] at this
    simp [Semiring.natCast_zero, Semiring.natCast_add, Semiring.natCast_one]
    replace this := OrderedAdd.add_le_left_iff 1 |>.mp this
    rw [Semiring.add_comm, Semiring.add_zero] at this
    exact Std.lt_of_lt_of_le zero_lt_one this
  next n ih m =>
    intro h
    replace ih := ih _ h
    simp [Semiring.natCast_add, Semiring.natCast_one]
    exact OrderedAdd.add_lt_left_iff _ |>.mp ih

theorem pos_natCast_of_pos (a : Nat) : 0 < a → 0 < (a : R) := by
  induction a
  next => simp
  next n ih =>
    simp; cases n
    next => simp +arith; rw [Semiring.natCast_one]; apply zero_lt_one
    next =>
      simp at ih
      replace ih := OrderedAdd.add_lt_add ih zero_lt_one
      rw [Semiring.add_zero, ← Semiring.natCast_one, ← Semiring.natCast_add] at ih
      assumption

theorem pos_intCast_of_pos (a : Int) : 0 < a → 0 < (a : R) := by
  cases a
  next n =>
    intro h
    replace h : 0 < n := by cases n; simp at h; simp
    replace h := pos_natCast_of_pos (R := R) _ h
    rw [Int.ofNat_eq_natCast, Ring.intCast_natCast]
    assumption
  next => omega

theorem neg_intCast_of_neg (a : Int) : a < 0 → (a : R) < 0 := by
  intro h
  have h : 0 < -a := by omega
  replace h := pos_intCast_of_pos (R := R) _ h
  simp [Ring.intCast_neg, OrderedAdd.neg_pos_iff] at h
  assumption

theorem nonneg_intCast_of_nonneg (a : Int) : 0 ≤ a → 0 ≤ (a : R) := by
  cases a
  next n =>
    intro; rw [Int.ofNat_eq_natCast, Ring.intCast_natCast]
    have := ofNat_nonneg (R := R) n
    rw [Semiring.ofNat_eq_natCast] at this
    assumption
  next => omega

theorem nonpos_intCast_of_nonpos (a : Int) : a ≤ 0 → (a : R) ≤ 0 := by
  intro h
  have h : 0 ≤ -a := by omega
  replace h := nonneg_intCast_of_nonneg (R := R) _ h
  simp [Ring.intCast_neg, OrderedAdd.neg_nonneg_iff] at h
  assumption

instance [Ring R] [LE R] [LT R] [LawfulOrderLT R] [IsPreorder R] [OrderedRing R] :
    IsCharP R 0 := IsCharP.mk' _ _ <| by
  intro x
  simp only [Nat.mod_zero]; constructor
  next =>
    intro h
    cases x
    next => rfl
    next x =>
      rw [Semiring.ofNat_succ] at h
      replace h := congrArg (· - 1) h; simp at h
      rw [Ring.sub_eq_add_neg, Semiring.add_assoc, AddCommGroup.add_neg_cancel,
          Ring.sub_eq_add_neg, AddCommMonoid.zero_add, Semiring.add_zero] at h
      have h₁ : (OfNat.ofNat x : R) < 0 := by
        have := OrderedRing.neg_one_lt_zero (R := R)
        rw [h]; assumption
      have h₂ := OrderedRing.ofNat_nonneg (R := R) x
      have : (0 : R) < 0 := Preorder.lt_of_le_of_lt h₂ h₁
      simp
      exact (Preorder.lt_irrefl 0) this
  next => intro h; rw [OfNat.ofNat, h]; rfl

end Preorder

theorem mul_pos [LE R] [LT R] [IsPreorder R] [OrderedRing R] {a b : R} (h₁ : 0 < a) (h₂ : 0 < b) : 0 < a * b := by
  simpa [Semiring.zero_mul] using mul_lt_mul_of_pos_right h₁ h₂

theorem zero_le_one [LE R] [LT R] [LawfulOrderLT R] [IsPreorder R] [OrderedRing R] : (0 : R) ≤ 1 :=
  Preorder.le_of_lt zero_lt_one

theorem not_one_lt_zero [LE R] [LT R] [LawfulOrderLT R] [IsPreorder R] [OrderedRing R] : ¬ ((1 : R) < 0) :=
  fun h => Preorder.lt_irrefl (0 : R) (Preorder.lt_trans zero_lt_one h)

section PartialOrder

variable [LE R] [LT R] [IsPartialOrder R] [OrderedRing R]

variable [LawfulOrderLT R]

theorem mul_le_mul_of_nonneg_left {a b c : R} (h : a ≤ b) (h' : 0 ≤ c) : c * a ≤ c * b := by
  rw [PartialOrder.le_iff_lt_or_eq] at h'
  cases h' with
  | inl h' =>
    have p := mul_lt_mul_of_pos_left (a := a) (b := b) (c := c)
    rw [PartialOrder.le_iff_lt_or_eq] at h
    cases h with
    | inl h => exact Preorder.le_of_lt (p h h')
    | inr h => subst h; exact le_refl (c * a)
  | inr h' => subst h'; simp [Semiring.zero_mul, le_refl]

theorem mul_le_mul_of_nonneg_right {a b c : R} (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  rw [PartialOrder.le_iff_lt_or_eq] at h'
  cases h' with
  | inl h' =>
    have p := mul_lt_mul_of_pos_right (a := a) (b := b) (c := c)
    rw [PartialOrder.le_iff_lt_or_eq] at h
    cases h with
    | inl h => exact Preorder.le_of_lt (p h h')
    | inr h => subst h; exact le_refl (a * c)
  | inr h' => subst h'; simp [Semiring.mul_zero, le_refl]

open OrderedAdd

theorem mul_le_mul_of_nonpos_left {a b c : R} (h : a ≤ b) (h' : c ≤ 0) : c * b ≤ c * a := by
  have := mul_le_mul_of_nonneg_left h (neg_nonneg_iff.mpr h')
  rwa [Ring.neg_mul, Ring.neg_mul, neg_le_iff, AddCommGroup.neg_neg] at this

theorem mul_le_mul_of_nonpos_right {a b c : R} (h : a ≤ b) (h' : c ≤ 0) : b * c ≤ a * c := by
  have := mul_le_mul_of_nonneg_right h (neg_nonneg_iff.mpr h')
  rwa [Ring.mul_neg, Ring.mul_neg, neg_le_iff, AddCommGroup.neg_neg] at this

theorem mul_lt_mul_of_neg_left {a b c : R} (h : a < b) (h' : c < 0) : c * b < c * a := by
  have := mul_lt_mul_of_pos_left h (neg_pos_iff.mpr h')
  rwa [Ring.neg_mul, Ring.neg_mul, neg_lt_iff, AddCommGroup.neg_neg] at this

theorem mul_lt_mul_of_neg_right {a b c : R} (h : a < b) (h' : c < 0) : b * c < a * c := by
  have := mul_lt_mul_of_pos_right h (neg_pos_iff.mpr h')
  rwa [Ring.mul_neg, Ring.mul_neg, neg_lt_iff, AddCommGroup.neg_neg] at this

theorem mul_nonneg {a b : R} (h₁ : 0 ≤ a) (h₂ : 0 ≤ b) : 0 ≤ a * b := by
  simpa [Semiring.zero_mul] using mul_le_mul_of_nonneg_right h₁ h₂

theorem mul_nonneg_of_nonpos_of_nonpos {a b : R} (h₁ : a ≤ 0) (h₂ : b ≤ 0) : 0 ≤ a * b := by
  have := mul_nonneg (neg_nonneg_iff.mpr h₁) (neg_nonneg_iff.mpr h₂)
  simpa [Ring.neg_mul, Ring.mul_neg, AddCommGroup.neg_neg] using this

theorem mul_nonpos_of_nonneg_of_nonpos {a b : R} (h₁ : 0 ≤ a) (h₂ : b ≤ 0) : a * b ≤ 0 := by
  rw [← neg_nonneg_iff, ← Ring.mul_neg]
  apply mul_nonneg h₁ (neg_nonneg_iff.mpr h₂)

theorem mul_nonpos_of_nonpos_of_nonneg {a b : R} (h₁ : a ≤ 0) (h₂ : 0 ≤ b) : a * b ≤ 0 := by
  rw [← neg_nonneg_iff, ← Ring.neg_mul]
  apply mul_nonneg (neg_nonneg_iff.mpr h₁) h₂

theorem mul_pos_of_neg_of_neg {a b : R} (h₁ : a < 0) (h₂ : b < 0) : 0 < a * b := by
  have := mul_pos (neg_pos_iff.mpr h₁) (neg_pos_iff.mpr h₂)
  simpa [Ring.neg_mul, Ring.mul_neg, AddCommGroup.neg_neg] using this

theorem mul_neg_of_pos_of_neg {a b : R} (h₁ : 0 < a) (h₂ : b < 0) : a * b < 0 := by
  rw [← neg_pos_iff, ← Ring.mul_neg]
  apply mul_pos h₁ (neg_pos_iff.mpr h₂)

theorem mul_neg_of_neg_of_pos {a b : R} (h₁ : a < 0) (h₂ : 0 < b) : a * b < 0 := by
  rw [← neg_pos_iff, ← Ring.neg_mul]
  apply mul_pos (neg_pos_iff.mpr h₁) h₂

end PartialOrder

section LinearOrder

variable [LE R] [LT R] [LawfulOrderLT R] [IsLinearOrder R] [OrderedRing R]

theorem mul_nonneg_iff {a b : R} : 0 ≤ a * b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  rcases LinearOrder.trichotomy 0 a with (ha | rfl | ha)
  · rcases LinearOrder.trichotomy 0 b with (hb | rfl | hb)
    · simp [Preorder.le_of_lt ha, Preorder.le_of_lt hb, mul_nonneg]
    · simp [Semiring.mul_zero, le_refl, le_total]
    · have m : a * b < 0 := mul_neg_of_pos_of_neg ha hb
      simp [Preorder.le_of_lt ha, Preorder.le_of_lt hb, Preorder.not_ge_of_lt m,
        Preorder.not_ge_of_lt ha, Preorder.not_ge_of_lt hb]
  · simp [Semiring.zero_mul, le_refl, le_total]
  · rcases LinearOrder.trichotomy 0 b with (hb | rfl | hb)
    · have m : a * b < 0 := mul_neg_of_neg_of_pos ha hb
      simp [Preorder.le_of_lt ha, Preorder.le_of_lt hb, Preorder.not_ge_of_lt m,
        Preorder.not_ge_of_lt ha, Preorder.not_ge_of_lt hb]
    · simp [Semiring.mul_zero, le_refl, le_total]
    · simp [Preorder.le_of_lt ha, Preorder.le_of_lt hb, mul_nonneg_of_nonpos_of_nonpos]

theorem mul_pos_iff {a b : R} : 0 < a * b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := by
  rcases LinearOrder.trichotomy 0 a with (ha | rfl | ha)
  · rcases LinearOrder.trichotomy 0 b with (hb | rfl | hb)
    · simp [ha, hb, mul_pos]
    · simp [Preorder.lt_irrefl, Semiring.mul_zero]
    · have m : a * b < 0 := mul_neg_of_pos_of_neg ha hb
      simp [ha, hb, Preorder.not_gt_of_lt m,
        Preorder.not_gt_of_lt ha, Preorder.not_gt_of_lt hb]
  · simp [Preorder.lt_irrefl, Semiring.zero_mul]
  · rcases LinearOrder.trichotomy 0 b with (hb | rfl | hb)
    · have m : a * b < 0 := mul_neg_of_neg_of_pos ha hb
      simp [ha, hb, Preorder.not_gt_of_lt m,
        Preorder.not_gt_of_lt ha, Preorder.not_gt_of_lt hb]
    · simp [Preorder.lt_irrefl, Semiring.mul_zero]
    · simp [ha, hb, mul_pos_of_neg_of_neg]

theorem sq_nonneg {a : R} : 0 ≤ a^2 := by
  rw [Semiring.pow_two, mul_nonneg_iff]
  rcases le_total (a := 0) (b := a) with (h | h)
  · exact .inl ⟨h, h⟩
  · exact .inr ⟨h, h⟩

theorem sq_pos {a : R} (h : a ≠ 0) : 0 < a^2 := by
  rw [Semiring.pow_two, mul_pos_iff]
  rcases LinearOrder.trichotomy 0 a with (h' | rfl | h')
  · exact .inl ⟨h', h'⟩
  · simp at h
  · exact .inr ⟨h', h'⟩

end LinearOrder

end OrderedRing

end Lean.Grind
