/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import Init.Data.Int.DivMod.Lemmas

/-!
# Typeclasses for types that can be embedded into an interval of `Int`.

The typeclass `ToInt α lo? hi?` carries the data of a function `ToInt.toInt : α → Int`
which is injective, lands between the (optional) lower and upper bounds `lo?` and `hi?`.

The function `ToInt.wrap` is the identity if either bound is `none`,
and otherwise wraps the integers into the interval `[lo, hi)`.

The typeclass `ToInt.Add α lo? hi?` then asserts that `toInt (x + y) = wrap lo? hi? (toInt x + toInt y)`.
There are many variants for other operations.

These typeclasses are used solely in the `grind` tactic to lift linear inequalities into `Int`.
-/

namespace Lean.Grind

class ToInt (α : Type u) (lo? hi? : outParam (Option Int)) where
  toInt : α → Int
  toInt_inj : ∀ x y, toInt x = toInt y → x = y
  le_toInt : lo? = some lo → lo ≤ toInt x
  toInt_lt : hi? = some hi → toInt x < hi

@[simp]
def ToInt.wrap (lo? hi? : Option Int) (x : Int) : Int :=
  match lo?, hi? with
  | some lo, some hi => (x - lo) % (hi - lo) + lo
  | _, _ => x

class ToInt.Zero (α : Type u) [Zero α] (lo? hi? : outParam (Option Int)) [ToInt α lo? hi?] where
  toInt_zero : toInt (0 : α) = wrap lo? hi? 0

class ToInt.Add (α : Type u) [Add α] (lo? hi? : outParam (Option Int)) [ToInt α lo? hi?] where
  toInt_add : ∀ x y : α, toInt (x + y) = wrap lo? hi? (toInt x + toInt y)

class ToInt.Neg (α : Type u) [Neg α] (lo? hi? : outParam (Option Int)) [ToInt α lo? hi?] where
  toInt_neg : ∀ x : α, toInt (-x) = wrap lo? hi? (-toInt x)

class ToInt.Sub (α : Type u) [Sub α] (lo? hi? : outParam (Option Int)) [ToInt α lo? hi?] where
  toInt_sub : ∀ x y : α, toInt (x - y) = wrap lo? hi? (toInt x - toInt y)

class ToInt.Mod (α : Type u) [Mod α] (lo? hi? : outParam (Option Int)) [ToInt α lo? hi?] where
  /-- One might expect a `wrap` on the right hand side,
  but in practice this stronger statement is usually true. -/
  toInt_mod : ∀ x y : α, toInt (x % y) = toInt x % toInt y

class ToInt.LE (α : Type u) [LE α] (lo? hi? : outParam (Option Int)) [ToInt α lo? hi?] where
  le_iff : ∀ x y : α, x ≤ y ↔ toInt x ≤ toInt y

class ToInt.LT (α : Type u) [LT α] (lo? hi? : outParam (Option Int)) [ToInt α lo? hi?] where
  lt_iff : ∀ x y : α, x < y ↔ toInt x < toInt y

/-! ## Helper theorems -/

theorem ToInt.wrap_add (lo? hi? : Option Int) (x y : Int) :
    ToInt.wrap lo? hi? (x + y) = ToInt.wrap lo? hi? (ToInt.wrap lo? hi? x + ToInt.wrap lo? hi? y) := by
  simp only [wrap]
  split <;> rename_i lo hi
  · dsimp
    rw [Int.add_left_inj, Int.emod_eq_emod_iff_emod_sub_eq_zero, Int.emod_def (x - lo), Int.emod_def (y - lo)]
    have : (x + y - lo -
        (x - lo - (hi - lo) * ((x - lo) / (hi - lo)) + lo +
          (y - lo - (hi - lo) * ((y - lo) / (hi - lo)) + lo) - lo)) =
        (hi - lo) * ((x - lo) / (hi - lo) + (y - lo) / (hi - lo)) := by
      simp only [Int.mul_add]
      omega
    rw [this]
    exact Int.mul_emod_right ..
  · simp

@[simp]
theorem ToInt.wrap_toInt (lo? hi? : Option Int) [ToInt α lo? hi?] (x : α) :
    ToInt.wrap lo? hi? (ToInt.toInt x) = ToInt.toInt x := by
  simp only [wrap]
  split
  · have := ToInt.le_toInt (x := x) rfl
    have := ToInt.toInt_lt (x := x) rfl
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    omega
  · rfl

theorem ToInt.wrap_eq_bmod {i : Int} (h : 0 ≤ i) :
    ToInt.wrap (some (-i)) (some i) x = x.bmod ((2 * i).toNat) := by
  match i, h with
  | (i : Nat), _ =>
    have : (2 * (i : Int)).toNat = 2 * i := by omega
    rw [this]
    simp [Int.bmod_eq_emod, ← Int.two_mul]
    have : (2 * (i : Int) + 1) / 2 = i := by omega
    rw [this]
    by_cases h : i = 0
    · simp [h]
    split
    · rw [← Int.sub_eq_add_neg, Int.sub_eq_iff_eq_add, Nat.two_mul, Int.natCast_add,
        ← Int.sub_sub, Int.sub_add_cancel]
      rw [Int.emod_eq_iff (by omega)]
      refine ⟨?_, ?_, ?_⟩
      · omega
      · have := Int.emod_lt x (b := 2 * (i : Int)) (by omega)
        omega
      · rw [Int.emod_def]
        have : x - 2 * ↑i * (x / (2 * ↑i)) - ↑i - (x + ↑i) = (2 * (i : Int)) * (- (x / (2 * i)) - 1) := by
          simp only [Int.mul_sub, Int.mul_neg]
          omega
        rw [this]
        exact Int.dvd_mul_right ..
    · rw [← Int.sub_eq_add_neg, Int.sub_eq_iff_eq_add, Int.natCast_zero, Int.sub_zero]
      rw [Int.emod_eq_iff (by omega)]
      refine ⟨?_, ?_, ?_⟩
      · have := Int.emod_nonneg x (b := 2 * (i : Int)) (by omega)
        omega
      · omega
      · rw [Int.emod_def]
        have : x - 2 * ↑i * (x / (2 * ↑i)) + ↑i - (x + ↑i) = (2 * (i : Int)) * (- (x / (2 * i))) := by
          simp only [Int.mul_neg]
          omega
        rw [this]
        exact Int.dvd_mul_right ..

theorem ToInt.wrap_eq_wrap_iff :
    ToInt.wrap (some lo) (some hi) x = ToInt.wrap (some lo) (some hi) y ↔ (x - y) % (hi - lo) = 0 := by
  simp only [wrap]
  rw [Int.add_left_inj]
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
  have : x - lo - (y - lo)  = x - y := by omega
  rw [this]

/-- Construct a `ToInt.Sub` instance from a `ToInt.Add` and `ToInt.Neg` instance and
a `sub_eq_add_neg` assumption. -/
def ToInt.Sub.of_sub_eq_add_neg {α : Type u} [_root_.Add α] [_root_.Neg α] [_root_.Sub α]
    (sub_eq_add_neg : ∀ x y : α, x - y = x + -y)
    {lo? hi? : Option Int} [ToInt α lo? hi?] [Add α lo? hi?] [Neg α lo? hi?] : ToInt.Sub α lo? hi? where
  toInt_sub x y := by
    rw [sub_eq_add_neg, ToInt.Add.toInt_add, ToInt.Neg.toInt_neg, Int.sub_eq_add_neg]
    conv => rhs; rw [ToInt.wrap_add, ToInt.wrap_toInt]

end Lean.Grind
