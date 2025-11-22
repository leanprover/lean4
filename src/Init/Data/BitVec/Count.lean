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
Count occurrences of a specific bit value.

Examples:
* `(0b1010#4).count true = 2`
* `(0b1010#4).count false = 2`
* `(0#3).count true = 0`
-/
def count (x : BitVec w) (b : Bool) : Nat :=
  x.countP (· == b)

@[simp]
theorem count_nil (b : Bool) : count nil b = 0 := by
  simp [count, -ofNat_eq_ofNat]

@[simp]
theorem count_cons (b : Bool) (c : Bool) (x : BitVec w) :
    count (cons b x) c = (if b == c then 1 else 0) + count x c := by
  simp [count]

/--
Population count: number of 1-bits (Hamming weight).

This is the number of bits set to `true` in the bitvector.

Examples:
* `(0b1010#4).popcount = 2`
* `(0b1111#4).popcount = 4`
* `(0#8).popcount = 0`

Note: This implementation could be optimized with a native `@[extern]` implementation
using efficient CPU instructions (e.g., GMP's `gmp_popcount` or x86's `POPCNT`).
See https://github.com/leanprover/lean4/issues/7887 for discussion of native implementations.
-/
def popcount (x : BitVec w) : Nat :=
  x.count true

@[simp]
theorem popcount_nil : popcount nil = 0 := by
  simp [popcount, -ofNat_eq_ofNat]

@[simp]
theorem popcount_cons (b : Bool) (x : BitVec w) :
    popcount (cons b x) = b.toNat + popcount x := by
  simp [popcount, count]
  cases b <;> simp

theorem popcount_eq_countP (x : BitVec w) : x.popcount = x.countP id := by
  simp [popcount, count, countP]

theorem popcount_eq_foldr (x : BitVec w) :
    x.popcount = x.foldr (fun b acc => b.toNat + acc) 0 := by
  simp only [popcount, count, countP, beq_true]
  congr
  ext b
  cases b <;> simp [Nat.add_comm]

/--
Count the number of `false` bits (zeros).

This is the complement of `popcount`.
-/
def zerocount (x : BitVec w) : Nat :=
  x.count false

@[simp]
theorem zerocount_nil : zerocount nil = 0 := by
  simp [zerocount, -ofNat_eq_ofNat]

@[simp]
theorem zerocount_cons (b : Bool) (x : BitVec w) :
    zerocount (cons b x) = (!b).toNat + zerocount x := by
  cases b <;> simp [zerocount, count]

theorem popcount_add_zerocount (x : BitVec w) : x.popcount + x.zerocount = w := by
  induction x using BitVec.induction with
  | nil => simp [-ofNat_eq_ofNat]
  | cons _ b => cases b <;> simp_all +arith

end BitVec
