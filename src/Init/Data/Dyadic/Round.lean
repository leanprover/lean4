/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.Data.Dyadic.Basic
import all Init.Data.Dyadic.Instances
import Init.Data.Int.Bitwise.Lemmas
import Init.Grind.Ordered.Rat
import Init.Grind.Ordered.Field

namespace Dyadic

/-!
Theorems about `roundUp` and `roundDown`.
-/

public section

theorem roundDown_le {x : Dyadic} {prec : Int} : roundDown x prec ≤ x :=
  match x with
  | .zero => Dyadic.le_refl _
  | .ofOdd n k _ => by
    unfold roundDown
    dsimp
    match h : k - prec with
    | .ofNat l =>
      dsimp
      rw [ofOdd_eq_ofIntWithPrec, le_iff_toRat]
      replace h : k = Int.ofNat l + prec := by omega
      subst h
      simp only [toRat_ofIntWithPrec_eq_mul_two_pow]
      rw [Int.neg_add, Rat.zpow_add (by decide), ← Rat.mul_assoc]
      refine Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_right ?_ (Rat.zpow_nonneg (by decide))
      rw [Int.shiftRight_eq_div_pow]
      rw [← Lean.Grind.Field.IsOrdered.mul_le_mul_iff_of_pos_right (c := 2^(Int.ofNat l)) (Rat.zpow_pos (by decide))]
      simp only [Int.natCast_pow, Int.cast_ofNat_Int, Int.ofNat_eq_coe]
      rw [Rat.mul_assoc, ← Rat.zpow_add (by decide), Int.add_left_neg, Rat.zpow_zero, Rat.mul_one]
      have : (2 : Rat) ^ (l : Int) = (2 ^ l : Int) := by
        rw [Rat.zpow_natCast, Rat.intCast_pow, Rat.intCast_ofNat]
      rw [this, ← Rat.intCast_mul, Rat.intCast_le_intCast]
      exact Int.ediv_mul_le n (Int.pow_ne_zero (by decide))
    | .negSucc _ =>
      apply Dyadic.le_refl

theorem precision_roundDown {x : Dyadic} {prec : Int} : (roundDown x prec).precision ≤ some prec := by
  unfold roundDown
  match x with
  | zero => simp [precision]
  | ofOdd n k hn =>
    dsimp
    split
    · rename_i n' h
      by_cases h' : n >>> n' = 0
      · simp [h']
      · exact precision_ofIntWithPrec_le h' _
    · simp [precision]
      omega

-- This theorem would characterize `roundDown` in terms of the order and `precision`.
-- theorem le_roundDown {x y : Dyadic} {prec : Int} (h : y.precision ≤ some prec) (h' : y ≤ x) :
--     y ≤ x.roundDown prec := sorry

theorem le_roundUp {x : Dyadic} {prec : Int} : x ≤ roundUp x prec := by
  rw [roundUp_eq_neg_roundDown_neg, Lean.Grind.OrderedAdd.le_neg_iff]
  apply roundDown_le

theorem precision_roundUp {x : Dyadic} {prec : Int} : (roundUp x prec).precision ≤ some prec := by
  rw [roundUp_eq_neg_roundDown_neg, precision_neg]
  exact precision_roundDown

-- This theorem would characterize `roundUp` in terms of the order and `precision`.
-- theorem roundUp_le {x y : Dyadic} {prec : Int} (h : y.precision ≤ some prec) (h' : x ≤ y) :
--    x.roundUp prec ≤ y := sorry
