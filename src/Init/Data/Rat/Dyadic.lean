/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.Data.Int.DivMod.Basic
public import Init.Data.Nat.Log2
public import Init.Data.Rat.Basic
meta import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Int

/-- The number of trailing zeros in the binary representation of `i`. -/
def trailingZeros (i : Int) : Nat :=
  aux i.natAbs.log2 i 0
where
  aux (k : Nat) (i : Int) (acc : Nat) : Nat :=
    match k with
    | 0 => acc
    | k+1 =>
      if i % 2 = 1 then acc
      else aux k (i / 2) (acc + 1)

example : trailingZeros 1 = 0 := by native_decide
example : trailingZeros 2 = 1 := by native_decide
example : trailingZeros 3 = 0 := by native_decide
example : trailingZeros 4 = 2 := by native_decide

theorem trailingZeros_two_mul_add_one (i : Int) : Int.trailingZeros (2 * i + 1) = 0 := sorry
theorem trailingZeros_two_mul (i : Int) : Int.trailingZeros (2 * i) = Int.trailingZeros i + 1 := sorry

/-- The unique representation of an integer as either zero, or an odd number times a power of two. -/
def toDyadic (i : Int) : Option (Int × Nat) :=
  if i = 0 then none
  else
    let k := i.trailingZeros
    some (i / (2 ^ (k + 1)), k)

def ofDyadic (x : Option (Int × Nat)) : Int :=
  match x with
  | none => 0
  | some (n, k) => (2 * n + 1) * 2 ^ k

theorem toDyadic_ofDyadic (x : Option (Int × Nat)) : toDyadic (ofDyadic x) = x := sorry
theorem ofDyadic_toDyadic (i : Int) : ofDyadic (toDyadic i) = i := sorry

example : toDyadic (ofDyadic none) = none := rfl
example : toDyadic (ofDyadic (some (7, 2))) = some (7, 2) := by native_decide
example : toDyadic (ofDyadic (some (-7, 2))) = some ((-7 : Int), 2) := by native_decide
example : ofDyadic (toDyadic 0) = 0 := rfl
example : ofDyadic (toDyadic 37) = 37 := by native_decide
example : ofDyadic (toDyadic (-37)) = -37 := by native_decide

/-- A dyadic rational is either zero or of the form `(2 * n + 1) / 2^k` for some (unique) `n k : Int`. -/
inductive Dyadic where
| zero
| of (n : Int) (k : Int)
deriving DecidableEq

namespace Dyadic

/--
Addition of dyadic rationals.
```
(2*n+1)/2^k + (2*m+1)/2^l = ((2*n+1)*2^l + (2*m+1)*2^k)/2^(k + l)
```
-/
def add (x y : Dyadic) : Dyadic :=
  match x, y with
  | .zero, _ => y
  | _, .zero => x
  | .of n (k : Nat), .of m (l : Nat) =>
    let n' := (2 * n + 1) * 2 ^ l + (2 * m + 1) * 2 ^ k
    match toDyadic n' with
    | none => .zero
    | some (n'', k') => .of n'' (k + l - k')
  | .of n (-((k : Nat) + 1)), .of m (l : Nat) =>
    let n' := (2 * n + 1) * 2 ^ (k + 1 + 1) + (2 * m + 1)
    match toDyadic n' with
    | none => .zero
    | some (n'', k') => .of n'' (l - k')
  | .of n (k : Nat), .of m (-((l : Nat) + 1)) =>
    let n' := (2 * n + 1) + (2 * m + 1) * 2 ^ (k + l + 1)
    match toDyadic n' with
    | none => .zero
    | some (n'', k') => .of n'' (k - k')
  | .of n (-((k : Nat) + 1)), .of m (-((l : Nat) + 1)) =>
    let n' := (2 * n + 1) * 2 ^ (k - l) + (2 * m + 1) * 2 ^ (l - k)
    match toDyadic n' with
    | none => .zero
    | some (n'', k') => .of n'' (- (min (k + 1) (l + 1)) - k')

instance : Add Dyadic := ⟨Dyadic.add⟩

def mul (x y : Dyadic) : Dyadic :=
  match x, y with
  | .zero, _ => .zero
  | _, .zero => .zero
  | .of n k, .of m l => .of (2 * n * m + (n + m)) (k + l)

instance : Mul Dyadic := ⟨Dyadic.mul⟩

def neg (x : Dyadic) : Dyadic :=
  match x with
  | .zero => .zero
  | .of n k => .of (- n - 1) k

instance : Neg Dyadic := ⟨Dyadic.neg⟩

def sub (x y : Dyadic) : Dyadic := x + (- y)

instance : Sub Dyadic := ⟨Dyadic.sub⟩

def toRat (x : Dyadic) : Rat :=
  match x with
  | .zero => 0
  | .of n (k : Nat) =>
    ⟨2 * n + 1, 2 ^ k, sorry, sorry⟩
  | .of n (-((k : Nat) + 1)) =>
    ⟨(2 * n + 1) * 2 ^ (k + 1), 1, sorry, sorry⟩

example : (Dyadic.of 1 2).add (.of 1 2) = .of 1 1 := by native_decide -- 3/4 + 3/4 = 3/2
example : (Dyadic.of 3 3).add (.of 0 3) = .of 0 0 := by native_decide -- 7/8 + 1/8 = 1
example : (Dyadic.of 1 (-2)).add (.of 1 1) = .of 13 1 := by native_decide -- 12 + 3/2 = 27/2 = (2 * 13 + 1)/2^1
example : (Dyadic.of 1 1).add (.of 1 (-2)) = .of 13 1 := by native_decide -- 3/2 + 12 = 27/2 = (2 * 13 + 1)/2^1
example : (Dyadic.of 1 (-2)).add (.of 1 (-2)) = .of 1 (-3) := by native_decide -- 12 + 12 = 24

theorem toRat_add (x y : Dyadic) : toRat (x + y) = toRat x + toRat y := sorry
theorem toRat_mul (x y : Dyadic) : toRat (x * y) = toRat x * toRat y := sorry
theorem toRat_neg (x : Dyadic) : toRat (-x) = - toRat x := sorry

-- Then that `toRat` is injective, and thus that `Dyadic` is a ring.

-- Define `blt` and `ble`, check they are compatible with `toRat`, and hence that we have `IsLinearOrder` and `IsOrderedRing`.

-- Approximate rationals arbitrarily closely by dyadic rationals.

end Dyadic
