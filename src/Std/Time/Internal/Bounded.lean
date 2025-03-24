/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Init.Omega
import Init.Data.Int.DivMod.Lemmas

namespace Std
namespace Time
namespace Internal

set_option linter.all true in

/--
A `Bounded` is represented by an `Int` that is constrained by a lower and higher bounded using some
relation `rel`. It includes all the integers that `rel lo val ∧ rel val hi`.
-/
def Bounded (rel : Int → Int → Prop) (lo : Int) (hi : Int) := { val : Int // rel lo val ∧ rel val hi }

namespace Bounded

@[always_inline]
instance : LE (Bounded rel n m) where
  le l r := l.val ≤ r.val

@[always_inline]
instance : LT (Bounded rel n m) where
  lt l r := l.val < r.val

@[always_inline]
instance : Repr (Bounded rel m n) where
  reprPrec n := reprPrec n.val

@[always_inline]
instance : BEq (Bounded rel n m) where
  beq x y := (x.val = y.val)

@[always_inline]
instance {x y : Bounded rel a b} : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.val ≤ y.val))

/--
A `Bounded` integer that the relation used is the the less-equal relation so, it includes all
integers that `lo ≤ val ≤ hi`.
-/
abbrev LE := @Bounded LE.le

/--
Casts the boundaries of the `Bounded` using equivalences.
-/
@[inline]
def cast {rel : Int → Int → Prop} {lo₁ lo₂ hi₁ hi₂ : Int} (h₁ : lo₁ = lo₂) (h₂ : hi₁ = hi₂) (b : Bounded rel lo₁ hi₁) : Bounded rel lo₂ hi₂ :=
  .mk b.val ⟨h₁ ▸ b.property.1, h₂ ▸ b.property.2⟩

/--
A `Bounded` integer that the relation used is the the less-than relation so, it includes all
integers that `lo < val < hi`.
-/
abbrev LT := @Bounded LT.lt

/--
Creates a new `Bounded` Integer.
-/
@[inline]
def mk {rel : Int → Int → Prop} (val : Int) (proof : rel lo val ∧ rel val hi) : @Bounded rel lo hi :=
  ⟨val, proof⟩

/--
Convert a `Int` to a `Bounded` if it checks.
-/
@[inline]
def ofInt? [DecidableRel rel] (val : Int) : Option (Bounded rel lo hi) :=
  if h : rel lo ↑val ∧ rel ↑val hi then
    some ⟨val, h⟩
  else
    none

namespace LE

/--
Convert a `Nat` to a `Bounded.LE` by wrapping it.
-/
@[inline]
def ofNatWrapping { lo hi : Int } (val : Int) (h : lo ≤ hi) : Bounded.LE lo hi := by
  let range := hi - lo + 1
  have range_pos := Int.add_pos_of_nonneg_of_pos (b := 1) (Int.sub_nonneg_of_le h) (by decide)
  have not_zero := Int.ne_iff_lt_or_gt.mpr (Or.inl range_pos)
  have mod_nonneg : 0 ≤ (val - lo) % range := Int.emod_nonneg (val - lo) not_zero.symm
  have add_nonneg : lo ≤ lo + (val - lo) % range := Int.le_add_of_nonneg_right mod_nonneg
  have mod_range : (val - lo) % (hi - lo + 1) < range := Int.emod_lt_of_pos (a := val - lo) range_pos
  refine ⟨((val - lo) % range + range) % range + lo, And.intro ?_ ?_⟩
  · simp_all [range]
    rw [Int.add_comm] at add_nonneg
    exact add_nonneg
  · apply Int.add_le_of_le_sub_right
    simp_all [range]
    exact Int.le_of_lt_add_one mod_range

instance {k : Nat} : OfNat (Bounded.LE lo (lo + k)) n where
  ofNat :=
    let h : lo ≤ lo + k := Int.le_add_of_nonneg_right (Int.ofNat_zero_le k)
    ofNatWrapping n h

instance {k : Nat} : Inhabited (Bounded.LE lo (lo + k)) where
  default :=
    let h : lo ≤ lo + k := Int.le_add_of_nonneg_right (Int.ofNat_zero_le k)
    ofNatWrapping lo h

/--
Creates a new `Bounded` integer that the relation is less-equal.
-/
@[inline]
def mk (val : Int) (proof : lo ≤ val ∧ val ≤ hi) : Bounded.LE lo hi :=
  ⟨val, proof⟩

/--
Creates a new `Bounded` integer that the relation is less-equal.
-/
@[inline]
def exact (val : Nat) : Bounded.LE val val :=
  ⟨val, by simp⟩

/--
Creates a new `Bounded` integer.
-/
@[inline]
def ofInt { lo hi : Int } (val : Int) : Option (Bounded.LE lo hi) :=
  if h : lo ≤ val ∧ val ≤ hi
    then some ⟨val, h⟩
    else none

/--
Convert a `Nat` to a `Bounded.LE`.
-/
@[inline]
def ofNat (val : Nat) (h : val ≤ hi) : Bounded.LE 0 hi :=
  Bounded.mk val (And.intro (Int.ofNat_zero_le val) (Int.ofNat_le.mpr h))

/--
Convert a `Nat` to a `Bounded.LE` if it checks.
-/
@[inline]
def ofNat? { hi : Nat } (val : Nat) : Option (Bounded.LE 0 hi) :=
  if h : val ≤ hi then
    ofNat val h
  else
    none

/--
Convert a `Nat` to a `Bounded.LE` using the lower boundary too.
-/
@[inline]
def ofNat' (val : Nat) (h : lo ≤ val ∧ val ≤ hi) : Bounded.LE lo hi :=
  Bounded.mk val (And.intro (Int.ofNat_le.mpr h.left) (Int.ofNat_le.mpr h.right))

/--
Convert a `Nat` to a `Bounded.LE` using the lower boundary too.
-/
@[inline]
def clip (val : Int) (h : lo ≤ hi) : Bounded.LE lo hi :=
  if h₀ : lo ≤ val then
    if h₁ : val ≤ hi
      then ⟨val, And.intro h₀ h₁⟩
      else ⟨hi, And.intro h (Int.le_refl hi)⟩
  else ⟨lo, And.intro (Int.le_refl lo) h⟩

/--
Convert a `Bounded.LE` to a Nat.
-/
@[inline]
def toNat (n : Bounded.LE lo hi) : Nat :=
  n.val.toNat

/--
Convert a `Bounded.LE` to a Nat.
-/
@[inline]
def toNat' (n : Bounded.LE lo hi) (h : lo ≥ 0) : Nat :=
  let h₁ := (Int.le_trans h n.property.left)
  match n.val, h₁ with
  | .ofNat n, _ => n
  | .negSucc _, h => by contradiction

/--
Convert a `Bounded.LE` to an Int.
-/
@[inline]
def toInt (n : Bounded.LE lo hi) : Int :=
  n.val

/--
Convert a `Bounded.LE` to a `Fin`.
-/
@[inline, simp]
def toFin (n : Bounded.LE lo hi) (h₀ : 0 ≤ lo) : Fin (hi + 1).toNat := by
  let h := n.property.right
  let h₁ := Int.le_trans h₀ n.property.left
  refine ⟨n.val.toNat, (Int.toNat_lt h₁).mpr ?_⟩
  rw [Int.toNat_of_nonneg (by omega)]
  exact Int.lt_add_one_of_le h

/--
Convert a `Fin` to a `Bounded.LE`.
-/
@[inline]
def ofFin (fin : Fin (Nat.succ hi)) : Bounded.LE 0 hi :=
  ofNat fin.val (Nat.le_of_lt_succ fin.isLt)

/--
Convert a `Fin` to a `Bounded.LE`.
-/
@[inline]
def ofFin' {lo : Nat} (fin : Fin (Nat.succ hi)) (h : lo ≤ hi) : Bounded.LE lo hi :=
  if h₁ : fin.val ≥ lo
    then ofNat' fin.val (And.intro h₁ ((Nat.le_of_lt_succ fin.isLt)))
    else ofNat' lo (And.intro (Nat.le_refl lo) h)

/--
Creates a new `Bounded.LE` using a the modulus of a number.
-/
@[inline]
def byEmod (b : Int) (i : Int) (hi : i > 0) : Bounded.LE 0 (i - 1) := by
  refine ⟨b % i, And.intro ?_ ?_⟩
  · apply Int.emod_nonneg b
    intro a
    simp_all [Int.lt_irrefl]
  · apply Int.le_of_lt_add_one
    simp [Int.add_sub_assoc]
    exact Int.emod_lt_of_pos b hi

/--
Creates a new `Bounded.LE` using a the Truncating modulus of a number.
-/
@[inline]
def byMod (b : Int) (i : Int) (hi : 0 < i) : Bounded.LE (- (i - 1)) (i - 1) := by
  refine ⟨b.tmod i, And.intro ?_ ?_⟩
  · simp [Int.tmod]
    split <;> try contradiction
    next m n =>
      let h := Int.emod_nonneg (a := m) (b := n) (Int.ne_of_gt hi)
      apply (Int.le_trans · h)
      apply Int.le_of_neg_le_neg
      simp_all
      exact (Int.le_sub_one_of_lt hi)
    next m n =>
      apply Int.neg_le_neg
      have h := Int.tmod_lt_of_pos (m + 1) hi
      exact Int.le_sub_one_of_lt h
  · exact Int.le_sub_one_of_lt (Int.tmod_lt_of_pos b hi)

/--
Adjust the bounds of a `Bounded` by setting the lower bound to zero and the maximum value to (m - n).
-/
@[inline]
def truncate (bounded : Bounded.LE n m) : Bounded.LE 0 (m - n) := by
  let ⟨left, right⟩ := bounded.property
  refine ⟨bounded.val - n, And.intro ?_ ?_⟩
  all_goals omega

/--
Adjust the bounds of a `Bounded` by changing the higher bound if another value `j` satisfies the same
constraint.
-/
@[inline, simp]
def truncateTop (bounded : Bounded.LE n m) (h : bounded.val ≤ j) : Bounded.LE n j := by
  refine ⟨bounded.val, And.intro ?_ ?_⟩
  · exact bounded.property.left
  · exact h

/--
Adjust the bounds of a `Bounded` by changing the lower bound if another value `j` satisfies the same
constraint.
-/
@[inline]
def truncateBottom (bounded : Bounded.LE n m) (h : bounded.val ≥ j) : Bounded.LE j m := by
  refine ⟨bounded.val, And.intro ?_ ?_⟩
  · exact h
  · exact bounded.property.right

/--
Adjust the bounds of a `Bounded` by adding a constant value to both the lower and upper bounds.
-/
@[inline]
def neg (bounded : Bounded.LE n m) : Bounded.LE (-m) (-n) := by
  refine ⟨-bounded.val, And.intro ?_ ?_⟩
  · exact Int.neg_le_neg bounded.property.right
  · exact Int.neg_le_neg bounded.property.left

/--
Adjust the bounds of a `Bounded` by adding a constant value to both the lower and upper bounds.
-/
@[inline, simp]
def add (bounded : Bounded.LE n m) (num : Int) : Bounded.LE (n + num) (m + num) := by
  refine ⟨bounded.val + num, And.intro ?_ ?_⟩
  all_goals apply (Int.add_le_add · (Int.le_refl num))
  · exact bounded.property.left
  · exact bounded.property.right

/--
Adjust the bounds of a `Bounded` by adding a constant value to both the lower and upper bounds.
-/
@[inline]
def addProven (bounded : Bounded.LE n m) (h₀ : bounded.val + num ≤ m) (h₁ : num ≥ 0) : Bounded.LE n m := by
  refine ⟨bounded.val + num, And.intro ?_ ?_⟩
  · exact Int.le_trans bounded.property.left (Int.le_add_of_nonneg_right h₁)
  · exact h₀

/--
Adjust the bounds of a `Bounded` by adding a constant value to the upper bounds.
-/
@[inline]
def addTop (bounded : Bounded.LE n m) (num : Int) (h : num ≥ 0) : Bounded.LE n (m + num) := by
  refine ⟨bounded.val + num, And.intro ?_ ?_⟩
  · let h := Int.add_le_add bounded.property.left h
    simp at h
    exact h
  · exact Int.add_le_add bounded.property.right (Int.le_refl num)

/--
Adjust the bounds of a `Bounded` by adding a constant value to the lower bounds.
-/
@[inline]
def subBottom (bounded : Bounded.LE n m) (num : Int) (h : num ≥ 0) : Bounded.LE (n - num) m := by
  refine ⟨bounded.val - num, And.intro ?_ ?_⟩
  · exact Int.add_le_add bounded.property.left (Int.le_refl (-num))
  · let h := Int.sub_le_sub bounded.property.right h
    simp at h
    exact h

/--
Adds two `Bounded` and adjust the boundaries.
-/
@[inline]
def addBounds (bounded : Bounded.LE n m) (bounded₂ : Bounded.LE i j) : Bounded.LE (n + i) (m + j) := by
  refine ⟨bounded.val + bounded₂.val, And.intro ?_ ?_⟩
  · exact Int.add_le_add bounded.property.left bounded₂.property.left
  · exact Int.add_le_add bounded.property.right bounded₂.property.right

/--
Adjust the bounds of a `Bounded` by subtracting a constant value to both the lower and upper bounds.
-/
@[inline, simp]
def sub (bounded : Bounded.LE n m) (num : Int) : Bounded.LE (n - num) (m - num) :=
  add bounded (-num)

/--
Adds two `Bounded` and adjust the boundaries.
-/
@[inline]
def subBounds (bounded : Bounded.LE n m) (bounded₂ : Bounded.LE i j) : Bounded.LE (n - j) (m - i) :=
  addBounds bounded bounded₂.neg

/--
Adjust the bounds of a `Bounded` by applying the emod operation constraining the lower bound to 0 and
the upper bound to the value.
-/
@[inline]
def emod (bounded : Bounded.LE n num) (num : Int) (hi : 0 < num) : Bounded.LE 0 (num - 1) :=
  byEmod bounded.val num hi

/--
Adjust the bounds of a `Bounded` by applying the mod operation.
-/
@[inline]
def mod (bounded : Bounded.LE n num) (num : Int) (hi : 0 < num) : Bounded.LE (- (num - 1)) (num - 1) :=
  byMod bounded.val num hi

/--
Adjust the bounds of a `Bounded` by applying the multiplication operation with a positive number.
-/
@[inline]
def mul_pos (bounded : Bounded.LE n m) (num : Int) (h : num ≥ 0) : Bounded.LE (n * num) (m * num) := by
  refine ⟨bounded.val * num, And.intro ?_ ?_⟩
  · exact Int.mul_le_mul_of_nonneg_right bounded.property.left h
  · exact Int.mul_le_mul_of_nonneg_right bounded.property.right h

/--
Adjust the bounds of a `Bounded` by applying the multiplication operation with a positive number.
-/
@[inline]
def mul_neg (bounded : Bounded.LE n m) (num : Int) (h : num ≤ 0) : Bounded.LE (m * num) (n * num) := by
  refine ⟨bounded.val * num, And.intro ?_ ?_⟩
  · exact Int.mul_le_mul_of_nonpos_right bounded.property.right h
  · exact Int.mul_le_mul_of_nonpos_right bounded.property.left h

/--
Adjust the bounds of a `Bounded` by applying the div operation.
-/
@[inline]
def ediv (bounded : Bounded.LE n m) (num : Int) (h : num > 0) : Bounded.LE (n / num) (m / num) := by
  let ⟨left, right⟩ := bounded.property
  refine ⟨bounded.val.ediv num, And.intro ?_ ?_⟩
  apply Int.ediv_le_ediv
  · exact h
  · exact left
  · apply Int.ediv_le_ediv
    · exact h
    · exact right

@[inline]
def eq {n : Int} : Bounded.LE n n :=
  ⟨n, And.intro (Int.le_refl n) (Int.le_refl n)⟩

/--
Expand the range of a bounded value.
-/
@[inline]
def expand (bounded : Bounded.LE lo hi) (h : hi ≤ nhi) (h₁ : nlo ≤ lo) : Bounded.LE nlo nhi :=
  ⟨bounded.val, And.intro (Int.le_trans h₁ bounded.property.left) (Int.le_trans bounded.property.right h)⟩

/--
Expand the bottom of the bounded to a number `nhi` is `hi` is less or equal to the previous higher bound.
-/
@[inline]
def expandTop (bounded : Bounded.LE lo hi) (h : hi ≤ nhi) : Bounded.LE lo nhi :=
  expand bounded h (Int.le_refl lo)

/--
Expand the bottom of the bounded to a number `nlo` if `lo` is greater or equal to the previous lower bound.
-/
@[inline]
def expandBottom (bounded : Bounded.LE lo hi) (h : nlo ≤ lo) : Bounded.LE nlo hi :=
  expand bounded (Int.le_refl hi) h

/--
Adds one to the value of the bounded if the value is less than the higher bound of the bounded number.
-/
@[inline]
def succ (bounded : Bounded.LE lo hi) (h : bounded.val < hi) : Bounded.LE lo hi :=
  let left := bounded.property.left
  ⟨bounded.val + 1, And.intro (by omega) (by omega)⟩

/--
Returns the absolute value of the bounded number `bo` with bounds `-(i - 1)` to `i - 1`. The result
will be a new bounded number with bounds `0` to `i - 1`.
-/
@[inline]
def abs (bo :  Bounded.LE (-i) i) : Bounded.LE 0 i :=
  if h : bo.val ≥ 0 then
    bo.truncateBottom h
  else by
    let r := bo.truncateTop (Int.le_of_lt (Int.not_le.mp h)) |>.neg
    rw [Int.neg_neg] at r
    exact r

/--
Returns the maximum between a number and the bounded.
-/
def max (bounded : Bounded.LE n m) (val : Int) : Bounded.LE (Max.max n val) (Max.max m val) := by
  let ⟨left, right⟩ := bounded.property
  refine ⟨Max.max bounded.val val, And.intro ?_ ?_⟩

  all_goals
    simp [Int.max_def]
    split <;> split

  next h => simp [h, Int.le_trans left h]
  next h h₁ => exact Int.le_of_lt <| Int.not_le.mp h₁
  next h => simp [h, Int.le_trans left h]
  next h h₁ => exact left
  next h h₁ => simp [h, Int.le_trans left h]
  next h h₁ => exact Int.le_of_lt <| Int.not_le.mp h₁
  next h h₁ =>
    let h₃ := Int.lt_of_lt_of_le (Int.not_le.mp h) right
    let h₄ := Int.not_le.mpr h₃ h₁
    contradiction
  next h h₁ => exact right

end LE
end Bounded
end Internal
end Time
end Std
