/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fady Adal
-/
module

prelude
public import Init.Data.BitVec.Basic
public import Init.Data.BitVec.Folds

public section

set_option linter.missingDocs true

namespace BitVec

/-!
## Counting and query operations

This module provides operations for counting and querying bits in bitvectors.
-/

/--
Count bits satisfying a predicate.

Examples:
* `(0b1010#4).countP id = 2` (count true bits)
* `(0b1010#4).countP not = 2` (count false bits)
* `(0#4).countP id = 0`
-/
def countP (x : BitVec w) (p : Bool → Bool) : Nat :=
  x.foldr (fun b acc => if p b then acc + 1 else acc) 0

@[simp]
theorem countP_nil (p : Bool → Bool) : countP nil p = 0 := by
  simp [countP, -ofNat_eq_ofNat]

@[simp]
theorem countP_cons (p : Bool → Bool) (b : Bool) (x : BitVec w) :
  countP (cons b x) p = (if p b then 1 else 0) + countP x p := by
    simp [countP]
    split <;> omega

/--
Population count: number of 1-bits (Hamming weight).

This is the number of bits set to `true` in the bitvector.

Examples:
* `(0b1010#4).popcount = 2`
* `(0b1111#4).popcount = 4`
* `(0#8).popcount = 0`

This function uses a native implementation with CPU popcount instructions when available.
-/
@[extern "lean_bitvec_popcount"]
def popcount (x : BitVec w) : Nat :=
  x.countP id

@[simp]
theorem popcount_nil : popcount nil = 0 := by
  simp [popcount, -ofNat_eq_ofNat]

@[simp]
theorem popcount_cons (b : Bool) (x : BitVec w) :
  popcount (cons b x) = b.toNat + popcount x := by
    simp only [popcount, countP, id_eq, foldr_cons]
    cases b <;> simp +arith

theorem popcount_le_width (x : BitVec w) : popcount x ≤ w := by
  induction x using BitVec.induction with
  | nil => simp [-ofNat_eq_ofNat]
  | cons _ b => cases b <;> simp_all +arith [Nat.le_succ_of_le]

theorem popcount_eq_foldr (x : BitVec w) :
  x.popcount = x.foldr (fun b acc => b.toNat + acc) 0 := by
    simp only [popcount, countP]
    congr
    ext b
    cases b <;> simp [Nat.add_comm]

@[simp]
theorem popcount_zero : popcount 0#w = 0 := by
  induction w with
  | zero => rw [eq_nil 0#0, popcount_nil]
  | succ => simpa [←false_cons_zero]

theorem popcount_eq_zero_iff {x : BitVec w} :
  popcount x = 0 ↔ x = 0#w := by
    constructor
    · intros
      induction x using BitVec.induction with
      | nil      => rfl
      | cons _ b => cases b <;> simp_all
    · intros; simp_all

@[simp]
theorem popcount_allOnes : popcount (allOnes w) = w := by
  induction w with
  | zero => rw [eq_nil (allOnes 0)]; simp [-ofNat_eq_ofNat]
  | succ => simpa +arith [←true_cons_allOnes]

theorem popcount_eq_width_iff {x : BitVec w} :
  popcount x = w ↔ x = allOnes w := by
    constructor
    · intros
      induction x using BitVec.induction with
      | nil => rfl
      | cons w' b x' ih =>
        have : x'.popcount ≤ w' := popcount_le_width _
        cases b <;> simp_all +arith [(by omega : x'.popcount ≠ w' + 1)]
    · intros; simp_all

/--
Count the number of `false` bits (zeros).

This is the complement of `popcount`.
-/
def zerocount (x : BitVec w) : Nat :=
  w - x.popcount

@[simp]
theorem zerocount_nil : zerocount nil = 0 := by
  simp [zerocount]

@[simp]
theorem zerocount_cons (b : Bool) (x : BitVec w) :
  zerocount (cons b x) = (!b).toNat + zerocount x := by
    cases b <;>
      simp +arith [zerocount, Nat.sub_add_comm (popcount_le_width _)]

theorem zerocount_eq_countP (x : BitVec w) :
  x.zerocount = x.countP not := by
    induction x using BitVec.induction with
    | nil => simp [-ofNat_eq_ofNat]
    | cons _ b => cases b <;> simp_all

theorem popcount_add_zerocount (x : BitVec w) :
  x.popcount + x.zerocount = w := by
    simp +arith [zerocount, popcount_le_width]

@[simp]
theorem zerocount_not {x : BitVec w} :
  (~~~x).zerocount = x.popcount := by
    induction x using BitVec.induction with
    | nil => simp [-ofNat_eq_ofNat]
    | cons _ b => cases b <;> simp_all

theorem popcount_not {x : BitVec w} :
  (~~~x).popcount = x.zerocount := by
    simp [←zerocount_not]

@[simp]
theorem zerocount_zero : zerocount 0#w = w := by
  simp [zerocount]

@[simp]
theorem zerocount_allOnes : zerocount (allOnes w) = 0 := by
  simp [zerocount]

theorem zerocount_le_width {x : BitVec w} : zerocount x ≤ w := by
  simp [zerocount]


/--
Count bits satisfying a predicate on both index and bit value.

This is useful when the position of bits matters, such as counting
set bits at odd/even positions or within specific bit ranges.

Examples:
* `x.countIdxP (fun i b => i.val % 2 = 1 && b)` - count true bits at odd positions
* `x.countIdxP (fun i b => b && (start ≤ i.val && i.val < end))` - count true bits in range
-/
def countIdxP (x : BitVec w) (p : Fin w → Bool → Bool) : Nat :=
  x.foldrIdx (fun i b acc => if p i b then acc + 1 else acc) 0

@[simp]
theorem countIdxP_nil (p : Fin 0 → Bool → Bool) : countIdxP nil p = 0 := by
  simp [countIdxP, -ofNat_eq_ofNat]

theorem countIdxP_cons (p : Fin (w+1) → Bool → Bool) (b : Bool) (x : BitVec w) :
    countIdxP (cons b x) p = (if p ⟨w, by omega⟩ b then 1 else 0) +
      countIdxP x (fun i bi => p ⟨i.val, by omega⟩ bi) := by
  simp only [countIdxP, foldrIdx_cons]
  split <;> simp +arith
  

end BitVec
