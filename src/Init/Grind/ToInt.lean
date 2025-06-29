/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.Data.Int.DivMod.Lemmas

public section

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

/-- An interval in the integers (either finite, half-infinite, or infinite). -/
inductive IntInterval : Type where
  | /-- The finite interval `[lo, hi)`. -/
    co (lo hi : Int)
  | /-- The half-infinite interval `[lo, ∞)`. -/
    ci (lo : Int)
  | /-- The half-infinite interval `(-∞, hi)`. -/
    io (hi : Int)
  | /-- The infinite interval `(-∞, ∞)`. -/
    ii
  deriving BEq, DecidableEq

instance : LawfulBEq IntInterval where
   rfl := by intro a; cases a <;> simp_all! [BEq.beq]
   eq_of_beq := by intro a b; cases a <;> cases b <;> simp_all! [BEq.beq]

namespace IntInterval

/-- The interval `[0, 2^n)`. -/
abbrev uint (n : Nat) := IntInterval.co 0 (2 ^ n)
/-- The interval `[-2^(n-1), 2^(n-1))`. -/
abbrev sint (n : Nat) := IntInterval.co (-(2 ^ (n - 1))) (2 ^ (n - 1))

/-- The lower bound of the interval, if finite. -/
def lo? (i : IntInterval) : Option Int :=
  match i with
  | co lo _ => some lo
  | ci lo => some lo
  | io _ => none
  | ii => none

/-- The upper bound of the interval, if finite. -/
def hi? (i : IntInterval) : Option Int :=
  match i with
  | co _ hi => some hi
  | ci _ => none
  | io hi => some hi
  | ii => none

@[simp]
def nonEmpty (i : IntInterval) : Bool :=
  match i with
  | co lo hi => lo < hi
  | ci _ => true
  | io _ => true
  | ii => true

@[simp]
def isFinite (i : IntInterval) : Bool :=
  match i with
  | co _ _ => true
  | ci _
  | io _
  | ii => false

def mem (i : IntInterval) (x : Int) : Prop :=
  match i with
  | co lo hi => lo ≤ x ∧ x < hi
  | ci lo => lo ≤ x
  | io hi => x < hi
  | ii => True

instance : Membership Int IntInterval where
  mem := mem

@[simp] theorem mem_co (lo hi : Int) (x : Int) : x ∈ IntInterval.co lo hi ↔ lo ≤ x ∧ x < hi := by rfl
@[simp] theorem mem_ci (lo : Int) (x : Int) : x ∈ IntInterval.ci lo ↔ lo ≤ x := by rfl
@[simp] theorem mem_io (hi : Int) (x : Int) : x ∈ IntInterval.io hi ↔ x < hi := by rfl
@[simp] theorem mem_ii (x : Int) : x ∈ IntInterval.ii ↔ True := by rfl

theorem nonEmpty_of_mem {x : Int} {i : IntInterval} (h : x ∈ i) : i.nonEmpty := by
  cases i <;> simp_all <;> omega

@[simp]
def wrap (i : IntInterval) (x : Int) : Int :=
  match i with
  | co lo hi => (x - lo) % (hi - lo) + lo
  | ci lo => max x lo
  | io hi => min x (hi - 1)
  | ii => x

theorem wrap_wrap (i : IntInterval) (x : Int) :
    wrap i (wrap i x) = wrap i x := by
  cases i <;> simp [wrap] <;> omega

theorem wrap_mem (i : IntInterval) (h : i.nonEmpty) (x : Int) :
    i.wrap x ∈ i := by
  match i with
  | co lo hi =>
    simp [wrap]
    simp at h
    constructor
    · apply Int.le_add_of_nonneg_left
      apply Int.emod_nonneg
      omega
    · have := Int.emod_lt (x - lo) (b := hi - lo) (by omega)
      omega
  | ci lo =>
    simp [wrap]
    omega
  | io hi =>
    simp [wrap]
    omega
  | ii =>
    simp [wrap]

theorem wrap_eq_self_iff (i : IntInterval) (h : i.nonEmpty) (x : Int) :
    i.wrap x = x ↔ x ∈ i := by
  match i with
  | co lo hi =>
    simp [wrap]
    simp at h
    constructor
    · have := Int.emod_lt (x - lo) (b := hi - lo) (by omega)
      have := Int.emod_nonneg (x - lo) (b := hi - lo) (by omega)
      omega
    · intro w
      rw [Int.emod_eq_of_lt] <;> omega
  | ci lo =>
    simp [wrap]
    omega
  | io hi =>
    simp [wrap]
    omega
  | ii =>
    simp [wrap]

theorem wrap_add {i : IntInterval} (h : i.isFinite) (x y : Int) :
    i.wrap (x + y) = i.wrap (i.wrap x + i.wrap y) := by
  match i with
  | co lo hi =>
    simp [wrap]
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero, Int.emod_def (x - lo), Int.emod_def (y - lo)]
    have : (x + y - lo - (x - lo - (hi - lo) * ((x - lo) / (hi - lo)) + lo + (y - lo - (hi - lo) * ((y - lo) / (hi - lo)) + lo) - lo)) =
      (hi - lo) * ((x - lo) / (hi - lo) + (y - lo) / (hi - lo)) := by
      simp only [Int.mul_add]
      omega
    rw [this]
    exact Int.mul_emod_right ..

theorem wrap_mul {i : IntInterval} (h : i.isFinite) (x y : Int) :
    i.wrap (x * y) = i.wrap (i.wrap x * i.wrap y) := by
  match i with
  | co lo hi =>
    dsimp [wrap]
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

theorem wrap_eq_bmod {i : Int} (h : 0 ≤ i) :
    (IntInterval.co (-i) i).wrap  x = x.bmod ((2 * i).toNat) := by
  dsimp only [wrap]
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

theorem wrap_eq_wrap_iff :
    (IntInterval.co lo hi).wrap x = (IntInterval.co lo hi).wrap y ↔ (x - y) % (hi - lo) = 0 := by
  simp only [wrap]
  rw [Int.add_left_inj]
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
  have : x - lo - (y - lo) = x - y := by omega
  rw [this]

end IntInterval

/--
`ToInt α I` asserts that `α` can be embedded faithfully into an interval `I` in the integers.
-/
class ToInt (α : Type u) (range : outParam IntInterval) where
  /-- The embedding function. -/
  toInt : α → Int
  /-- The embedding function is injective. -/
  toInt_inj : ∀ x y, toInt x = toInt y → x = y
  /-- The embedding function lands in the interval. -/
  toInt_mem : ∀ x, toInt x ∈ range

/--
The embedding into the integers takes `0` to `0`.
-/
class ToInt.Zero (α : Type u) [Zero α] (I : outParam IntInterval) [ToInt α I] where
  /-- The embedding takes `0` to `0`. -/
  toInt_zero : toInt (0 : α) = 0

/--
The embedding into the integers takes numerals in the range interval to themselves.
-/
class ToInt.OfNat (α : Type u) [∀ n, OfNat α n] (I : outParam IntInterval) [ToInt α I] where
  /-- The embedding takes `OfNat` to `OfNat`. -/
  toInt_ofNat : ∀ n : Nat, toInt (OfNat.ofNat n : α) = I.wrap n

/--
The embedding into the integers takes addition to addition, wrapped into the range interval.
-/
class ToInt.Add (α : Type u) [Add α] (I : outParam IntInterval) [ToInt α I] where
  /-- The embedding takes addition to addition, wrapped into the range interval. -/
  toInt_add : ∀ x y : α, toInt (x + y) = I.wrap (toInt x + toInt y)

/--
The embedding into the integers takes negation to negation, wrapped into the range interval.
-/
class ToInt.Neg (α : Type u) [Neg α] (I : outParam IntInterval) [ToInt α I] where
  /-- The embedding takes negation to negation, wrapped into the range interval. -/
  toInt_neg : ∀ x : α, toInt (-x) = I.wrap (-toInt x)

/--
The embedding into the integers takes subtraction to subtraction, wrapped into the range interval.
-/
class ToInt.Sub (α : Type u) [Sub α] (I : outParam IntInterval) [ToInt α I] where
  /-- The embedding takes subtraction to subtraction, wrapped into the range interval. -/
  toInt_sub : ∀ x y : α, toInt (x - y) = I.wrap (toInt x - toInt y)

/--
The embedding into the integers takes multiplication to multiplication, wrapped into the range interval.
-/
class ToInt.Mul (α : Type u) [Mul α] (I : outParam IntInterval) [ToInt α I] where
  /-- The embedding takes multiplication to multiplication, wrapped into the range interval. -/
  toInt_mul : ∀ x y : α, toInt (x * y) = I.wrap (toInt x * toInt y)

/--
The embedding into the integers takes exponentiation to exponentiation, wrapped into the range interval.
-/
class ToInt.Pow (α : Type u) [HPow α Nat α] (I : outParam IntInterval) [ToInt α I] where
  /-- The embedding takes exponentiation to exponentiation, wrapped into the range interval. -/
  toInt_pow : ∀ x : α, ∀ n : Nat, toInt (x ^ n) = I.wrap (toInt x ^ n)

/--
The embedding into the integers takes modulo to modulo (without needing to wrap into the range interval).
-/
class ToInt.Mod (α : Type u) [Mod α] (I : outParam IntInterval) [ToInt α I] where
  /--
  The embedding takes modulo to modulo (without needing to wrap into the range interval).
  One might expect a `wrap` on the right hand side,
  but in practice this stronger statement is usually true.
  -/
  toInt_mod : ∀ x y : α, toInt (x % y) = toInt x % toInt y

/--
The embedding into the integers takes division to division, wrapped into the range interval.
-/
class ToInt.Div (α : Type u) [Div α] (I : outParam IntInterval) [ToInt α I] where
  /--
  The embedding takes division to division (without needing to wrap into the range interval).
  One might expect a `wrap` on the right hand side,
  but in practice this stronger statement is usually true.
  -/
  toInt_div : ∀ x y : α, toInt (x / y) = toInt x / toInt y

/--
The embedding into the integers is monotone.
-/
class ToInt.LE (α : Type u) [LE α] (I : outParam IntInterval) [ToInt α I] where
  /-- The embedding is monotone with respect to `≤`. -/
  le_iff : ∀ x y : α, x ≤ y ↔ toInt x ≤ toInt y

/--
The embedding into the integers is strictly monotone.
-/
class ToInt.LT (α : Type u) [LT α] (I : outParam IntInterval) [ToInt α I] where
  /-- The embedding is strictly monotone with respect to `<`. -/
  lt_iff : ∀ x y : α, x < y ↔ toInt x < toInt y

open IntInterval
namespace ToInt

/-! ## Helper theorems -/

theorem Zero.wrap_zero (I : IntInterval) [_root_.Zero α] [ToInt α I] [ToInt.Zero α I] :
    I.wrap 0 = 0 := by
  have := toInt_mem (0 : α)
  rw [I.wrap_eq_self_iff (I.nonEmpty_of_mem this)]
  rwa [ToInt.Zero.toInt_zero] at this

@[simp]
theorem wrap_toInt (I : IntInterval) [ToInt α I] (x : α) :
    I.wrap (toInt x) = toInt x := by
  rw [I.wrap_eq_self_iff (I.nonEmpty_of_mem (toInt_mem x))]
  exact ToInt.toInt_mem x

/-- Construct a `ToInt.Sub` instance from a `ToInt.Add` and `ToInt.Neg` instance and
a `sub_eq_add_neg` assumption. -/
def Sub.of_sub_eq_add_neg {α : Type u} [_root_.Add α] [_root_.Neg α] [_root_.Sub α]
    (sub_eq_add_neg : ∀ x y : α, x - y = x + -y)
    {I : IntInterval} (h : I.isFinite) [ToInt α I] [Add α I] [Neg α I] : ToInt.Sub α I where
  toInt_sub x y := by
    rw [sub_eq_add_neg, ToInt.Add.toInt_add, ToInt.Neg.toInt_neg, Int.sub_eq_add_neg]
    conv => rhs; rw [wrap_add h, ToInt.wrap_toInt]

end ToInt

/-
Remark: `↑a` is notation for `ToInt.toInt a`.
We want to hide `Lean.Grind.ToInt.toInt` applications in the counterexamples produced by
the `cutsat` procedure in `grind`.
-/
@[app_unexpander ToInt.toInt]
meta def toIntUnexpander : PrettyPrinter.Unexpander := fun stx => do
  match stx with
  | `($_ $a:term) => `(↑$a)
  | _ => throw ()

end Lean.Grind
