/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fady Adal
-/
module

prelude
public import Init.Data.BitVec.Count
public import Init.Data.BitVec.Folds
public import Init.Data.BitVec.Map

public section

set_option linter.missingDocs true

namespace BitVec

/-!
## Hamming distance and related operations

This module provides operations related to Hamming distance and bitwise metrics,
useful in coding theory and error detection applications.
-/

/--
Bitwise dot product: count of positions where both bits are 1.

This is equivalent to `popcount (x &&& y)` and useful for computing
similarity between bitvectors.

Examples:
* `dot 0b1100#4 0b1010#4 = 1` (only position 3 has both bits set)
* `dot 0b1111#4 0b1111#4 = 4` (all positions match)
* `dot x y ≤ min (popcount x) (popcount y)`
-/
def dot (x y : BitVec w) : Nat :=
  (x &&& y).popcount

@[simp]
theorem dot_nil : dot nil nil = 0 := by
  simp [dot, -ofNat_eq_ofNat]

@[simp]
theorem dot_cons (a b : Bool) (x y : BitVec w) :
  dot (cons a x) (cons b y) = (if a && b then 1 else 0) + dot x y := by
    simp only [dot, cons_and_cons, popcount_cons,
               Bool.and_eq_true, Nat.add_right_cancel_iff]
    split <;> simp_all

theorem dot_comm (x y : BitVec w) : dot x y = dot y x := by
  simp [dot, and_comm]

theorem dot_zero_left (x : BitVec w) : dot 0#w x = 0 := by
  simp [dot]

@[simp]
theorem dot_zero_right (x : BitVec w) : dot x 0#w = 0 := by
  simp [dot]

theorem dot_le_popcount_left (x y : BitVec w) :
  dot x y ≤ x.popcount := by
  induction x using BitVec.induction with
  | nil => simp [-ofNat_eq_ofNat, eq_nil y]
  | cons w' b x' ih =>
    rw [←cons_msb_setWidth y]
    simp only [dot_cons, Bool.and_eq_true, popcount_cons]
    cases b <;> cases y.msb <;> simp_all +arith [Nat.le_succ_iff]

theorem dot_le_popcount_right (x y : BitVec w) :
  dot x y ≤ y.popcount := 
    dot_comm .. ▸ dot_le_popcount_left ..

@[simp]
theorem dot_allOnes_left (x : BitVec w) : dot (allOnes w) x = x.popcount := by
  induction w with
  | zero => rw [eq_nil (allOnes 0), eq_nil x, dot_nil, popcount_nil]
  | succ w' ih =>
    rw [←true_cons_allOnes, ←(cons_msb_setWidth x), dot_cons]
    cases x.msb <;> simp_all

theorem dot_allOnes_right (x : BitVec w) :
  dot x (allOnes w) = x.popcount := 
    dot_comm .. ▸ dot_allOnes_left ..

/--
Hamming distance: number of positions where bits differ.

This is the standard metric for measuring distance between two bitvectors,
defined as `popcount (x ^^^ y)`.

The Hamming distance is a metric satisfying:
- Non-negativity: `hammingDist x y ≥ 0`
- Symmetry: `hammingDist x y = hammingDist y x`
- Triangle inequality: `hammingDist x z ≤ hammingDist x y + hammingDist y z`
- Identity of indiscernibles: `hammingDist x y = 0 ↔ x = y`

Examples:
* `hammingDist 0b1100#4 0b1010#4 = 2` (differ at positions 0 and 2)
* `hammingDist x x = 0` (a bitvector has distance 0 from itself)
* `hammingDist 0#4 (~~~(0#4)) = 4` (maximum distance)
-/
def hammingDist (x y : BitVec w) : Nat :=
  (x ^^^ y).popcount

@[simp]
theorem hammingDist_nil : hammingDist nil nil = 0 := by
  simp [hammingDist, ←ofNat_eq_ofNat]

@[simp]
theorem hammingDist_cons (a b : Bool) (x y : BitVec w) :
    hammingDist (cons a x) (cons b y) = (if a != b then 1 else 0) + hammingDist x y := by
  simp only [hammingDist, cons_xor_cons, popcount_cons, bne_iff_ne, ne_eq, ite_not,
    Nat.add_right_cancel_iff]
  split <;> simpa

theorem hammingDist_comm (x y : BitVec w) : hammingDist x y = hammingDist y x := by
  simp [hammingDist, xor_comm]

@[simp]
theorem hammingDist_self (x : BitVec w) : hammingDist x x = 0 := by
  simp [hammingDist, -ofNat_eq_ofNat]

theorem hammingDist_eq_zero_iff (x y : BitVec w) :
  hammingDist x y = 0 ↔ x = y := by
    constructor
    · intros
      apply BitVec.xor_eq_zero_iff.mp <| popcount_eq_zero_iff.mp ‹_›
    · intros; simp_all

theorem hammingDist_le_width (x y : BitVec w) :
  hammingDist x y ≤ w := by
    simp [hammingDist, popcount_le_width]

theorem hammingDist_triangle (x y z : BitVec w) :
  hammingDist x z ≤ hammingDist x y + hammingDist y z := by
    induction w with
    | zero => rw [eq_nil x, eq_nil y, eq_nil z]; simp
    | succ w' ih =>
      rw [←cons_msb_setWidth x, ←cons_msb_setWidth y, ←cons_msb_setWidth z]
      cases x.msb <;> cases y.msb <;> cases z.msb <;>
        simp_all +arith [-cons_msb_setWidth, Nat.le_add_right_of_le]

theorem hammingDist_not (x y : BitVec w) :
  hammingDist (~~~x) (~~~y) = hammingDist x y := by
    induction w with
    | zero => rw [eq_nil x, eq_nil y]; simp
    | succ w' ih =>
      rw [←cons_msb_setWidth x, ←cons_msb_setWidth y]
      cases x.msb <;> cases y.msb <;> simp_all [-cons_msb_setWidth]


theorem hammingDist_zero_left (x : BitVec w) : hammingDist 0 x = x.popcount := by
  simp [hammingDist]

theorem hammingDist_zero_right (x : BitVec w) : hammingDist x 0 = x.popcount := by
  simp [hammingDist]

theorem hammingDist_allOnes_left (x : BitVec w) : hammingDist (allOnes w) x = x.zerocount := by
  simp [hammingDist, popcount_not]

theorem hammingDist_allOnes_right (x : BitVec w) : hammingDist x (allOnes w) = x.zerocount := by
  rw [hammingDist_comm, hammingDist_allOnes_left]

/--
Parity: whether the bitvector has an odd number of 1-bits.

Returns `true` if `popcount x` is odd, `false` if even.

This is equivalent to XOR reduction of all bits: `foldr xor false`.

Parity is used in:
- Simple error detection (parity bits)
- Quantum computing (phase estimation)
- Hash functions

Examples:
* `parity 0b1010#4 = false` (2 ones, even)
* `parity 0b1011#4 = true` (3 ones, odd)
* `parity 0#n = false` (0 ones, even)
-/
def parity (x : BitVec w) : Bool :=
  x.foldr xor false

@[simp]
theorem parity_nil : parity nil = false := by
  simp [parity, -ofNat_eq_ofNat]


@[simp]
theorem parity_cons (b : Bool) (x : BitVec w) :
  parity (cons b x) = (b ^^ (parity x)) := by
    cases b <;> simp [parity]

theorem parity_eq_popcount_mod (x : BitVec w) :
  parity x = (x.popcount % 2 == 1) := by
    induction x using BitVec.induction with
    | nil => simp [-ofNat_eq_ofNat]
    | cons w' b x' ih => 
      cases hb : b <;> cases hx' : x'.parity <;> simp_all [Nat.add_mod]

theorem parity_xor (x y : BitVec w) :
  parity (x ^^^ y) = ((parity x) ^^ (parity y)) := by
    induction w with
    | zero => rw [eq_nil x, eq_nil y]; simp [←ofNat_eq_ofNat]
    | succ w' ih =>
      rw [←cons_msb_setWidth x, ←cons_msb_setWidth y]
      cases y.msb <;> simp_all [-cons_msb_setWidth]
    

@[simp]
theorem parity_zero : parity 0#w = false := by
  simp [parity_eq_popcount_mod 0#w]

theorem parity_not (x : BitVec w) :
  parity (~~~x) = ((w % 2 == 1) ^^ (parity x)) := by
    induction x using BitVec.induction with
    | nil => simp
    | cons w' b x' ih =>
      have : (w' % 2 == 1) = !(w' + 1) % 2 == 1 := by
        cases Nat.mod_two_eq_zero_or_one w' <;> simp_all [Nat.add_mod]
      cases hb : b <;> cases hx' : x'.parity <;> simp_all

theorem parity_allOnes : parity (allOnes w) = (w % 2 == 1) := by
  rw [←not_not (b := allOnes w), not_allOnes, parity_not]
  simp

end BitVec
