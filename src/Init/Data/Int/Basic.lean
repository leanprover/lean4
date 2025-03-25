/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

The integers, with addition, multiplication, and subtraction.
-/
prelude
import Init.Data.Cast
import Init.Data.Nat.Div.Basic

set_option linter.missingDocs true -- keep it documented
open Nat

/-! # Integer Type, Coercions, and Notation

This file defines the `Int` type as well as

* coercions, conversions, and compatibility with numeric literals,
* basic arithmetic operations add/sub/mul/pow,
* a few `Nat`-related operations such as `negOfNat` and `subNatNat`,
* relations `<`/`≤`/`≥`/`>`, the `NonNeg` property and `min`/`max`,
* decidability of equality, relations and `NonNeg`.

Division and modulus operations are defined in `Init.Data.Int.DivMod.Basic`.
-/

/--
The integers.

This type is special-cased by the compiler and overridden with an efficient implementation. The
runtime has a special representation for `Int` that stores “small” signed numbers directly, while
larger numbers use a fast arbitrary-precision arithmetic library (usually
[GMP](https://gmplib.org/)). A “small number” is an integer that can be encoded with one fewer bits
than the platform's pointer size (i.e. 63 bits on 64-bit architectures and 31 bits on 32-bit
architectures).
-/
inductive Int : Type where
  /--
  A natural number is an integer.

  This constructor covers the non-negative integers (from `0` to `∞`).
  -/
  | ofNat   : Nat → Int
  /--
  The negation of the successor of a natural number is an integer.

  This constructor covers the negative integers (from `-1` to `-∞`).
  -/
  | negSucc : Nat → Int

attribute [extern "lean_nat_to_int"] Int.ofNat
attribute [extern "lean_int_neg_succ_of_nat"] Int.negSucc

instance : NatCast Int where natCast n := Int.ofNat n

instance instOfNat : OfNat Int n where
  ofNat := Int.ofNat n

namespace Int

/--
`-[n+1]` is suggestive notation for `negSucc n`, which is the second constructor of
`Int` for making strictly negative numbers by mapping `n : Nat` to `-(n + 1)`.
-/
scoped notation "-[" n "+1]" => negSucc n

instance : Inhabited Int := ⟨ofNat 0⟩

@[simp] theorem default_eq_zero : default = (0 : Int) := rfl

protected theorem zero_ne_one : (0 : Int) ≠ 1 := nofun

/-! ## Coercions -/

@[simp] theorem ofNat_eq_coe : Int.ofNat n = Nat.cast n := rfl

@[simp] theorem ofNat_zero : ((0 : Nat) : Int) = 0 := rfl

@[simp] theorem ofNat_one  : ((1 : Nat) : Int) = 1 := rfl

theorem ofNat_two : ((2 : Nat) : Int) = 2 := rfl

/--
Negation of natural numbers.

Examples:
 * `Int.negOfNat 6 = -6`
 * `Int.negOfNat 0 = 0`
-/
def negOfNat : Nat → Int
  | 0      => 0
  | succ m => negSucc m

set_option bootstrap.genMatcherCode false in
/--
Negation of integers, usually accessed via the `-` prefix operator.

This function is overridden by the compiler with an efficient implementation. This definition is
the logical model.

Examples:
 * `-(6 : Int) = -6`
 * `-(-6 : Int) = 6`
 * `(12 : Int).neg = -12`
-/
@[extern "lean_int_neg"]
protected def neg (n : @& Int) : Int :=
  match n with
  | ofNat n   => negOfNat n
  | negSucc n => succ n

/-
  The `Neg Int` default instance must have priority higher than `low`
  since the default instance `OfNat Nat n` has `low` priority.

  ```
  #check -42
  ```
-/
@[default_instance mid]
instance instNegInt : Neg Int where
  neg := Int.neg

/--
Non-truncating subtraction of two natural numbers.

Examples:
 * `Int.subNatNat 5 2 = 3`
 * `Int.subNatNat 2 5 = -3`
 * `Int.subNatNat 0 13 = -13`
-/
def subNatNat (m n : Nat) : Int :=
  match (n - m : Nat) with
  | 0        => ofNat (m - n)  -- m ≥ n
  | (succ k) => negSucc k

set_option bootstrap.genMatcherCode false in
/--
Addition of integers, usually accessed via the `+` operator.

This function is overridden by the compiler with an efficient implementation. This definition is
the logical model.

Examples:
 * `(7 : Int) + (6 : Int) = 13`
 * `(6 : Int) + (-6 : Int) = 0`
-/
@[extern "lean_int_add"]
protected def add (m n : @& Int) : Int :=
  match m, n with
  | ofNat m, ofNat n => ofNat (m + n)
  | ofNat m, -[n +1] => subNatNat m (succ n)
  | -[m +1], ofNat n => subNatNat n (succ m)
  | -[m +1], -[n +1] => negSucc (succ (m + n))

instance : Add Int where
  add := Int.add

set_option bootstrap.genMatcherCode false in
/--
Multiplication of integers, usually accessed via the `*` operator.

This function is overridden by the compiler with an efficient implementation. This definition is
the logical model.

Examples:
 * `(63 : Int) * (6 : Int) = 378`
 * `(6 : Int) * (-6 : Int) = -36`
 * `(7 : Int) * (0 : Int) = 0`
-/
@[extern "lean_int_mul"]
protected def mul (m n : @& Int) : Int :=
  match m, n with
  | ofNat m, ofNat n => ofNat (m * n)
  | ofNat m, -[n +1] => negOfNat (m * succ n)
  | -[m +1], ofNat n => negOfNat (succ m * n)
  | -[m +1], -[n +1] => ofNat (succ m * succ n)

instance : Mul Int where
  mul := Int.mul


/--
Subtraction of integers, usually accessed via the `-` operator.

This function is overridden by the compiler with an efficient implementation. This definition is
the logical model.

Examples:
* `(63 : Int) - (6 : Int) = 57`
* `(7 : Int) - (0 : Int) = 7`
* `(0 : Int) - (7 : Int) = -7`
-/
@[extern "lean_int_sub"]
protected def sub (m n : @& Int) : Int := m + (- n)

instance : Sub Int where
  sub := Int.sub

/--
An integer is non-negative if it is equal to a natural number.
-/
inductive NonNeg : Int → Prop where
  /--
  For all natural numbers `n`, `Int.ofNat n` is non-negative.
  -/
  | mk (n : Nat) : NonNeg (ofNat n)

/--
Non-strict inequality of integers, usually accessed via the `≤` operator.

`a ≤ b` is defined as `b - a ≥ 0`, using `Int.NonNeg`.
-/
protected def le (a b : Int) : Prop := NonNeg (b - a)

instance instLEInt : LE Int where
  le := Int.le

/--
Strict inequality of integers, usually accessed via the `<` operator.

`a < b` when `a + 1 ≤ b`.
-/
protected def lt (a b : Int) : Prop := (a + 1) ≤ b

instance instLTInt : LT Int where
  lt := Int.lt

set_option bootstrap.genMatcherCode false in
/--
Decides whether two integers are equal. Usually accessed via the `DecidableEq Int` instance.

This function is overridden by the compiler with an efficient implementation. This definition is the
logical model.

Examples:
* `show (7 : Int) = (3 : Int) + (4 : Int) by decide`
* `if (6 : Int) = (3 : Int) * (2 : Int) then "yes" else "no" = "yes"`
* `(¬ (6 : Int) = (3 : Int)) = true`
-/
@[extern "lean_int_dec_eq"]
protected def decEq (a b : @& Int) : Decidable (a = b) :=
  match a, b with
  | ofNat a, ofNat b => match decEq a b with
    | isTrue h  => isTrue  <| h ▸ rfl
    | isFalse h => isFalse <| fun h' => Int.noConfusion h' (fun h' => absurd h' h)
  | ofNat _, -[_ +1] => isFalse <| fun h => Int.noConfusion h
  | -[_ +1], ofNat _ => isFalse <| fun h => Int.noConfusion h
  | -[a +1], -[b +1] => match decEq a b with
    | isTrue h  => isTrue  <| h ▸ rfl
    | isFalse h => isFalse <| fun h' => Int.noConfusion h' (fun h' => absurd h' h)

@[inherit_doc Int.decEq]
instance : DecidableEq Int := Int.decEq

set_option bootstrap.genMatcherCode false in
/-- Decides whether an integer is negative.

  ```
  #eval (7 : Int).decNonneg.decide -- true
  #eval (0 : Int).decNonneg.decide -- true
  #eval ¬ (-7 : Int).decNonneg.decide -- true
  ```

  Implemented by efficient native code. -/
@[extern "lean_int_dec_nonneg"]
private def decNonneg (m : @& Int) : Decidable (NonNeg m) :=
  match m with
  | ofNat m => isTrue <| NonNeg.mk m
  | -[_ +1] => isFalse <| fun h => nomatch h

/-- Decides whether `a ≤ b`.

  ```
  #eval ¬ ( (7 : Int) ≤ (0 : Int) ) -- true
  #eval (0 : Int) ≤ (0 : Int) -- true
  #eval (7 : Int) ≤ (10 : Int) -- true
  ```

  Implemented by efficient native code. -/
@[extern "lean_int_dec_le"]
instance decLe (a b : @& Int) : Decidable (a ≤ b) :=
  decNonneg _

/-- Decides whether `a < b`.

  ```
  #eval `¬ ( (7 : Int) < 0 )` -- true
  #eval `¬ ( (0 : Int) < 0 )` -- true
  #eval `(7 : Int) < 10` -- true
  ```

  Implemented by efficient native code. -/
@[extern "lean_int_dec_lt"]
instance decLt (a b : @& Int) : Decidable (a < b) :=
  decNonneg _

set_option bootstrap.genMatcherCode false in
/--
The absolute value of an integer is its distance from `0`.

This function is overridden by the compiler with an efficient implementation. This definition is
the logical model.

Examples:
 * `(7 : Int).natAbs = 7`
 * `(0 : Int).natAbs = 0`
 * `((-11 : Int).natAbs = 11`
-/
@[extern "lean_nat_abs"]
def natAbs (m : @& Int) : Nat :=
  match m with
  | ofNat m => m
  | -[m +1] => m.succ

/-! ## sign -/

/--
Returns the “sign” of the integer as another integer:
 * `1` for positive numbers,
 * `-1` for negative numbers, and
 * `0` for `0`.

Examples:
 * `Int.sign 34 = 1`
 * `Int.sign 2 = 1`
 * `Int.sign 0 = 0`
 * `Int.sign -1 = -1`
 * `Int.sign -362 = -1`
-/
def sign : Int → Int
  | Int.ofNat (succ _) => 1
  | Int.ofNat 0 => 0
  | -[_+1]      => -1

/-! ## Conversion -/

/--
Converts an integer into a natural number. Negative numbers are converted to `0`.

Examples:
* `(7 : Int).toNat = 7`
* `(0 : Int).toNat = 0`
* `(-7 : Int).toNat = 0`
-/
def toNat : Int → Nat
  | ofNat n   => n
  | negSucc _ => 0

/--
Converts an integer into a natural number. Returns `none` for negative numbers.

Examples:
* `(7 : Int).toNat? = some 7`
* `(0 : Int).toNat? = some 0`
* `(-7 : Int).toNat? = none`
-/
def toNat? : Int → Option Nat
  | (n : Nat) => some n
  | -[_+1] => none

@[deprecated toNat? (since := "2025-03-11"), inherit_doc toNat?]
abbrev toNat' := toNat?

/-! ## divisibility -/

/--
Divisibility of integers. `a ∣ b` (typed as `\|`) says that
there is some `c` such that `b = a * c`.
-/
instance : Dvd Int where
  dvd a b := Exists (fun c => b = a * c)

/-! ## Powers -/

/--
Power of an integer to a natural number, usually accessed via the `^` operator.

Examples:
* `(2 : Int) ^ 4 = 16`
* `(10 : Int) ^ 0 = 1`
* `(0 : Int) ^ 10 = 0`
* `(-7 : Int) ^ 3 = -343`
-/
protected def pow (m : Int) : Nat → Int
  | 0      => 1
  | succ n => Int.pow m n * m

instance : NatPow Int where
  pow := Int.pow

instance : LawfulBEq Int where
  eq_of_beq h := by simp [BEq.beq] at h; assumption
  rfl := by simp [BEq.beq]

instance : Min Int := minOfLe

instance : Max Int := maxOfLe

end Int

/--
The canonical homomorphism `Int → R`. In most use cases, the target type will have a ring structure,
and this homomorphism should be a ring homomorphism.

`IntCast` and `NatCast` exist to allow different libraries with their own types that can be notated
as natural numbers to have consistent `simp` normal forms without needing to create coercion
simplification sets that are aware of all combinations. Libraries should make it easy to work with
`IntCast` where possible. For instance, in Mathlib there will be such a homomorphism (and thus an
`IntCast R` instance) whenever `R` is an additive group with a `1`.
-/
class IntCast (R : Type u) where
  /-- The canonical map `Int → R`. -/
  protected intCast : Int → R

instance : IntCast Int where intCast n := n

@[coe, reducible, match_pattern, inherit_doc IntCast]
protected def Int.cast {R : Type u} [IntCast R] : Int → R :=
  IntCast.intCast

-- see the notes about coercions into arbitrary types in the module doc-string
instance [IntCast R] : CoeTail Int R where coe := Int.cast

-- see the notes about coercions into arbitrary types in the module doc-string
instance [IntCast R] : CoeHTCT Int R where coe := Int.cast
