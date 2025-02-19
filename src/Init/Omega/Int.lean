/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Int.DivMod
import Init.Data.Int.Order

/-!
# Lemmas about `Nat`, `Int`, and `Fin` needed internally by `omega`.

These statements are useful for constructing proof expressions,
but unlikely to be widely useful, so are inside the `Lean.Omega` namespace.

If you do find a use for them, please move them into the appropriate file and namespace!
-/

namespace Lean.Omega

namespace Int

theorem ofNat_pow (a b : Nat) : ((a ^ b : Nat) : Int) = (a : Int) ^ b := by
  induction b with
  | zero => rfl
  | succ b ih => rw [Nat.pow_succ, Int.ofNat_mul, ih]; rfl

theorem pos_pow_of_pos (a : Int) (b : Nat) (h : 0 < a) : 0 < a ^ b := by
  rw [Int.eq_natAbs_of_zero_le (Int.le_of_lt h), ← Int.ofNat_zero, ← Int.ofNat_pow, Int.ofNat_lt]
  exact Nat.pow_pos (Int.natAbs_pos.mpr (Int.ne_of_gt h))

theorem ofNat_pos {a : Nat} : 0 < (a : Int) ↔ 0 < a := by
  rw [← Int.ofNat_zero, Int.ofNat_lt]

theorem ofNat_pos_of_pos {a : Nat} (h : 0 < a) : 0 < (a : Int) :=
  ofNat_pos.mpr h

theorem natCast_ofNat {x : Nat} :
    @Nat.cast Int instNatCastInt (no_index (OfNat.ofNat x)) = OfNat.ofNat x := rfl

theorem ofNat_lt_of_lt {x y : Nat} (h : x < y) : (x : Int) < (y : Int) :=
  Int.ofNat_lt.mpr h

theorem ofNat_le_of_le {x y : Nat} (h : x ≤ y) : (x : Int) ≤ (y : Int) :=
  Int.ofNat_le.mpr h

theorem ofNat_shiftLeft_eq {x y : Nat} : (x <<< y : Int) = (x : Int) * (2 ^ y : Nat) := by
  simp [Nat.shiftLeft_eq]

theorem ofNat_shiftRight_eq_div_pow {x y : Nat} : (x >>> y : Int) = (x : Int) / (2 ^ y : Nat) := by
  simp only [Nat.shiftRight_eq_div_pow, Int.ofNat_ediv]

theorem emod_ofNat_nonneg {x : Nat} {y : Int} : 0 ≤ (x : Int) % y :=
  Int.ofNat_zero_le _

-- FIXME these are insane:
theorem lt_of_not_ge {x y : Int} (h : ¬ (x ≤ y)) : y < x := Int.not_le.mp h
theorem lt_of_not_le {x y : Int} (h : ¬ (x ≤ y)) : y < x := Int.not_le.mp h
theorem not_le_of_lt {x y : Int} (h : y < x) : ¬ (x ≤ y) := Int.not_le.mpr h
theorem lt_le_asymm {x y : Int} (h₁ : y < x) (h₂ : x ≤ y) : False := Int.not_le.mpr h₁ h₂
theorem le_lt_asymm {x y : Int} (h₁ : y ≤ x) (h₂ : x < y) : False := Int.not_lt.mpr h₁ h₂

theorem le_of_not_gt {x y : Int} (h : ¬ (y > x)) : y ≤ x := Int.not_lt.mp h
theorem not_lt_of_ge {x y : Int} (h : y ≥ x) : ¬ (y < x) := Int.not_lt.mpr h
theorem le_of_not_lt {x y : Int} (h : ¬ (x < y)) : y ≤ x := Int.not_lt.mp h
theorem not_lt_of_le {x y : Int} (h : y ≤ x) : ¬ (x < y) := Int.not_lt.mpr h

theorem add_congr {a b c d : Int} (h₁ : a = b) (h₂ : c = d) : a + c = b + d := by
  subst h₁; subst h₂; rfl

theorem mul_congr {a b c d : Int} (h₁ : a = b) (h₂ : c = d) : a * c = b * d := by
  subst h₁; subst h₂; rfl

theorem mul_congr_left {a b : Int} (h₁ : a = b)  (c : Int) : a * c = b * c := by
  subst h₁; rfl

theorem sub_congr {a b c d : Int} (h₁ : a = b) (h₂ : c = d) : a - c = b - d := by
  subst h₁; subst h₂; rfl

theorem neg_congr {a b : Int} (h₁ : a = b) : -a = -b := by
  subst h₁; rfl

theorem lt_of_gt {x y : Int} (h : x > y) : y < x := gt_iff_lt.mp h
theorem le_of_ge {x y : Int} (h : x ≥ y) : y ≤ x := ge_iff_le.mp h

theorem ofNat_mul_nonneg {a b : Nat} : 0 ≤ (a : Int) * b := by
  rw [← Int.ofNat_mul]
  exact Int.ofNat_zero_le (a * b)

theorem ofNat_sub_eq_zero {b a : Nat} (h : ¬ b ≤ a) : ((a - b : Nat) : Int) = 0 :=
  Int.ofNat_eq_zero.mpr (Nat.sub_eq_zero_of_le (Nat.le_of_lt (Nat.not_le.mp h)))

theorem ofNat_sub_dichotomy {a b : Nat} :
    b ≤ a ∧ ((a - b : Nat) : Int) = a - b ∨ a < b ∧ ((a - b : Nat) : Int) = 0 := by
  by_cases h : b ≤ a
  · left
    have t := Int.ofNat_sub h
    simp at t
    exact ⟨h, t⟩
  · right
    have t := Nat.not_le.mp h
    simp [Int.ofNat_sub_eq_zero h]
    exact t

theorem ofNat_congr {a b : Nat} (h : a = b) : (a : Int) = (b : Int) := congrArg _ h

theorem ofNat_sub_sub {a b c : Nat} : ((a - b - c : Nat) : Int) = ((a - (b + c) : Nat) : Int) :=
  congrArg _ (Nat.sub_sub _ _ _)

theorem ofNat_min (a b : Nat) : ((min a b : Nat) : Int) = min (a : Int) (b : Int) := by
  simp only [Nat.min_def, Int.min_def, Int.ofNat_le]
  split <;> rfl

theorem ofNat_max (a b : Nat) : ((max a b : Nat) : Int) = max (a : Int) (b : Int) := by
  simp only [Nat.max_def, Int.max_def, Int.ofNat_le]
  split <;> rfl

theorem ofNat_natAbs (a : Int) : (a.natAbs : Int) = if 0 ≤ a then a else -a := by
  rw [Int.natAbs.eq_def]
  split <;> rename_i n
  · simp only [Int.ofNat_eq_coe]
    rw [if_pos (Int.ofNat_nonneg n)]
  · simp; rfl

theorem natAbs_dichotomy {a : Int} : 0 ≤ a ∧ a.natAbs = a ∨ a < 0 ∧ a.natAbs = -a := by
  by_cases h : 0 ≤ a
  · left
    simp_all [Int.natAbs_of_nonneg]
  · right
    rw [Int.not_le] at h
    rw [Int.ofNat_natAbs_of_nonpos (Int.le_of_lt h)]
    simp_all

theorem neg_le_natAbs {a : Int} : -a ≤ a.natAbs := by
  have t := Int.le_natAbs (a := -a)
  simp at t
  exact t

theorem add_le_iff_le_sub {a b c : Int} : a + b ≤ c ↔ a ≤ c - b := by
  conv =>
    lhs
    rw [← Int.add_zero c, ← Int.sub_self (-b), Int.sub_eq_add_neg, ← Int.add_assoc, Int.neg_neg,
      Int.add_le_add_iff_right]
  rfl

theorem le_add_iff_sub_le {a b c : Int} : a ≤ b + c ↔ a - c ≤ b := by
  conv =>
    lhs
    rw [← Int.neg_neg c, ← Int.sub_eq_add_neg, ← add_le_iff_le_sub]
  rfl

theorem add_le_zero_iff_le_neg {a b : Int} : a + b ≤ 0 ↔ a ≤ - b := by
  rw [add_le_iff_le_sub, Int.zero_sub]
theorem add_le_zero_iff_le_neg' {a b : Int} : a + b ≤ 0 ↔ b ≤ -a := by
  rw [Int.add_comm, add_le_zero_iff_le_neg]
theorem add_nonnneg_iff_neg_le {a b : Int} : 0 ≤ a + b ↔ -b ≤ a := by
  rw [le_add_iff_sub_le, Int.zero_sub]
theorem add_nonnneg_iff_neg_le' {a b : Int} : 0 ≤ a + b ↔ -a ≤ b := by
  rw [Int.add_comm, add_nonnneg_iff_neg_le]

theorem ofNat_fst_mk {β} {x : Nat} {y : β} : (Prod.mk x y).fst = (x : Int) := rfl
theorem ofNat_snd_mk {α} {x : α} {y : Nat} : (Prod.mk x y).snd = (y : Int) := rfl


end Int

namespace Nat

theorem lt_of_gt {x y : Nat} (h : x > y) : y < x := gt_iff_lt.mp h
theorem le_of_ge {x y : Nat} (h : x ≥ y) : y ≤ x := ge_iff_le.mp h

end Nat

namespace Fin

theorem ne_iff_lt_or_gt {i j : Fin n} : i ≠ j ↔ i < j ∨ i > j := by
  cases i; cases j; simp only [ne_eq, Fin.mk.injEq, Nat.ne_iff_lt_or_gt, gt_iff_lt]; rfl

protected theorem lt_or_gt_of_ne {i j : Fin n} (h : i ≠ j) : i < j ∨ i > j := Fin.ne_iff_lt_or_gt.mp h

theorem not_le {i j : Fin n} : ¬ i ≤ j ↔ j < i := by
  cases i; cases j; exact Nat.not_le

theorem not_lt {i j : Fin n} : ¬ i < j ↔ j ≤ i := by
  cases i; cases j; exact Nat.not_lt

protected theorem lt_of_not_le {i j : Fin n} (h : ¬ i ≤ j) : j < i := Fin.not_le.mp h
protected theorem le_of_not_lt {i j : Fin n} (h : ¬ i < j) : j ≤ i := Fin.not_lt.mp h

theorem ofNat_val_add {x y : Fin n} :
    (((x + y : Fin n)) : Int) = ((x : Int) + (y : Int)) % n := rfl

theorem ofNat_val_sub {x y : Fin n} :
    (((x - y : Fin n)) : Int) = (((n - y : Nat) + (x : Int) : Int)) % n := rfl

theorem ofNat_val_mul {x y : Fin n} :
    (((x * y : Fin n)) : Int) = ((x : Int) * (y : Int)) % n := rfl

theorem ofNat_val_natCast {n x y : Nat} (h : y = x % (n + 1)):
    @Nat.cast Int instNatCastInt (@Fin.val (n + 1) (OfNat.ofNat x)) = OfNat.ofNat y := by
  rw [h]
  rfl

end Fin

namespace Prod

theorem of_lex (w : Prod.Lex r s p q) : r p.fst q.fst ∨ p.fst = q.fst ∧ s p.snd q.snd :=
  Prod.lex_def.mp w

theorem of_not_lex {α} {r : α → α → Prop} [DecidableEq α] {β} {s : β → β → Prop}
    {p q : α × β} (w : ¬ Prod.Lex r s p q) :
    ¬ r p.fst q.fst ∧ (p.fst ≠ q.fst ∨ ¬ s p.snd q.snd) := by
  rw [Prod.lex_def, not_or, Decidable.not_and_iff_or_not_not] at w
  exact w

theorem fst_mk : (Prod.mk x y).fst = x := rfl
theorem snd_mk : (Prod.mk x y).snd = y := rfl

end Prod

end Lean.Omega
