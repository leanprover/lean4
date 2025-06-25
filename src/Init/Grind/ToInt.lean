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

/--
`ToInt α lo? hi?` asserts that `α` can be embedded faithfully into the interval `[lo, hi)` in the integers,
when `lo? = some lo` and `hi? = some hi`, and similarly can be embedded into a half-infinite or infinite interval when
`lo? = none` or `hi? = none`.
-/
class ToInt (α : Type u) (lo? hi? : outParam (Option Int)) where
  /-- The embedding function. -/
  toInt : α → Int
  /-- The embedding function is injective. -/
  toInt_inj : ∀ x y, toInt x = toInt y → x = y
  /-- The lower bound, if present, gives a lower bound on the embedding function. -/
  le_toInt : lo? = some lo → lo ≤ toInt x
  /-- The upper bound, if present, gives an upper bound on the embedding function. -/
  toInt_lt : hi? = some hi → toInt x < hi

@[simp]
def ToInt.wrap (lo? hi? : Option Int) (x : Int) : Int :=
  match lo?, hi? with
  | some lo, some hi => (x - lo) % (hi - lo) + lo
  | _, _ => x

/--
The embedding into the integers takes `0` to `0`.
-/
class ToInt.Zero (α : Type u) [Zero α] (lo? hi? : outParam (Option Int)) [ToInt α lo? hi?] where
  /-- The embedding takes `0` to `0`. -/
  toInt_zero : toInt (0 : α) = 0

/--
The embedding into the integers takes addition to addition, wrapped into the range interval.
-/
class ToInt.Add (α : Type u) [Add α] (lo? hi? : outParam (Option Int)) [ToInt α lo? hi?] where
  /-- The embedding takes addition to addition, wrapped into the range interval. -/
  toInt_add : ∀ x y : α, toInt (x + y) = wrap lo? hi? (toInt x + toInt y)

/--
The embedding into the integers takes negation to negation, wrapped into the range interval.
-/
class ToInt.Neg (α : Type u) [Neg α] (lo? hi? : outParam (Option Int)) [ToInt α lo? hi?] where
  /-- The embedding takes negation to negation, wrapped into the range interval. -/
  toInt_neg : ∀ x : α, toInt (-x) = wrap lo? hi? (-toInt x)

/--
The embedding into the integers takes subtraction to subtraction, wrapped into the range interval.
-/
class ToInt.Sub (α : Type u) [Sub α] (lo? hi? : outParam (Option Int)) [ToInt α lo? hi?] where
  /-- The embedding takes subtraction to subtraction, wrapped into the range interval. -/
  toInt_sub : ∀ x y : α, toInt (x - y) = wrap lo? hi? (toInt x - toInt y)

/--
The embedding into the integers takes multiplication to multiplication, wrapped into the range interval.
-/
class ToInt.Mul (α : Type u) [Mul α] (lo? hi? : outParam (Option Int)) [ToInt α lo? hi?] where
  /-- The embedding takes multiplication to multiplication, wrapped into the range interval. -/
  toInt_mul : ∀ x y : α, toInt (x * y) = wrap lo? hi? (toInt x * toInt y)

/--
The embedding into the integers takes exponentiation to exponentiation, wrapped into the range interval.
-/
class ToInt.Pow (α : Type u) [Pow α Nat] (lo? hi? : outParam (Option Int)) [ToInt α lo? hi?] where
  /-- The embedding takes exponentiation to exponentiation, wrapped into the range interval. -/
  toInt_pow : ∀ x : α, ∀ n : Nat, toInt (x ^ n) = wrap lo? hi? (toInt x ^ n)

/--
The embedding into the integers takes modulo to modulo (without needing to wrap into the range interval).
-/
class ToInt.Mod (α : Type u) [Mod α] (lo? hi? : outParam (Option Int)) [ToInt α lo? hi?] where
  /--
  The embedding takes modulo to modulo (without needing to wrap into the range interval).
  One might expect a `wrap` on the right hand side,
  but in practice this stronger statement is usually true.
  -/
  toInt_mod : ∀ x y : α, toInt (x % y) = toInt x % toInt y

/--
The embedding into the integers takes division to division, wrapped into the range interval.
-/
class ToInt.Div (α : Type u) [Div α] (lo? hi? : outParam (Option Int)) [ToInt α lo? hi?] where
  /--
  The embedding takes division to division (without needing to wrap into the range interval).
  One might expect a `wrap` on the right hand side,
  but in practice this stronger statement is usually true.
  -/
  toInt_div : ∀ x y : α, toInt (x / y) = toInt x / toInt y

/--
The embedding into the integers is monotone.
-/
class ToInt.LE (α : Type u) [LE α] (lo? hi? : outParam (Option Int)) [ToInt α lo? hi?] where
  /-- The embedding is monotone with respect to `≤`. -/
  le_iff : ∀ x y : α, x ≤ y ↔ toInt x ≤ toInt y

/--
The embedding into the integers is strictly monotone.
-/
class ToInt.LT (α : Type u) [LT α] (lo? hi? : outParam (Option Int)) [ToInt α lo? hi?] where
  /-- The embedding is strictly monotone with respect to `<`. -/
  lt_iff : ∀ x y : α, x < y ↔ toInt x < toInt y

/-! ## Helper theorems -/

theorem ToInt.Zero.wrap_zero (lo? hi? : Option Int) [_root_.Zero α] [ToInt α lo? hi?] [ToInt.Zero α lo? hi?] :
    ToInt.wrap lo? hi? (0 : Int) = 0 := by
  match hlo : lo?, hhi : hi? with
  | some lo, some hi =>
    subst hlo hhi
    have h := ToInt.Zero.toInt_zero (α := α)
    have hlo:= ToInt.le_toInt (x := (0 : α)) (lo := lo) rfl
    have hhi := ToInt.toInt_lt (x := (0 : α)) (hi := hi) rfl
    simp only [h] at hlo hhi
    unfold wrap
    simp only [Int.zero_sub]
    rw [Int.emod_eq_of_lt] <;> all_goals omega
  | some lo, none
  | none, some hi
  | none, none => rfl

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

theorem ToInt.wrap_mul (lo? hi? : Option Int) (x y : Int) :
    ToInt.wrap lo? hi? (x * y) = ToInt.wrap lo? hi? (ToInt.wrap lo? hi? x * ToInt.wrap lo? hi? y) := by
  simp only [wrap]
  split <;> rename_i lo hi
  · dsimp
    rw [Int.add_left_inj, Int.emod_eq_emod_iff_emod_sub_eq_zero, Int.emod_def (x - lo), Int.emod_def (y - lo)]
    have : x - lo - (hi - lo) * ((x - lo) / (hi - lo)) + lo = x - (hi - lo) * ((x - lo) / (hi - lo)) := by omega
    rw [this]; clear this
    have : y - lo - (hi - lo) * ((y - lo) / (hi - lo)) + lo = y - (hi - lo) * ((y - lo) / (hi - lo)) := by omega
    rw [this]; clear this
    have : x * y - lo - ((x - (hi - lo) * ((x - lo) / (hi - lo))) * (y - (hi - lo) * ((y - lo) / (hi - lo))) - lo) =
      x * y - (x - (hi - lo) * ((x - lo) / (hi - lo))) * (y - (hi - lo) * ((y - lo) / (hi - lo))) := by omega
    rw [this]; clear this
    have : (x - (hi - lo) * ((x - lo) / (hi - lo))) * (y - (hi - lo) * ((y - lo) / (hi - lo))) =
        x * y - (hi - lo) * (x * ((y - lo) / (hi - lo)) + (x - lo) / (hi - lo) * (y - (hi - lo) * ((y - lo) / (hi - lo)))) := by
      conv => lhs; rw [Int.sub_mul, Int.mul_sub, Int.mul_left_comm, Int.sub_sub, Int.mul_assoc, ← Int.mul_add]
    rw [this]; clear this
    rw [Int.sub_sub_self]
    apply Int.mul_emod_right
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
