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
The type of integers. It is defined as an inductive type based on the
natural number type `Nat` featuring two constructors: "a natural
number is an integer", and "the negation of a successor of a natural
number is an integer". The former represents integers between `0`
(inclusive) and `∞`, and the latter integers between `-∞` and `-1`
(inclusive).

This type is special-cased by the compiler. The runtime has a special
representation for `Int` which stores "small" signed numbers directly,
and larger numbers use an arbitrary precision "bignum" library
(usually [GMP](https://gmplib.org/)). A "small number" is an integer
that can be encoded with 63 bits (31 bits on 32-bits architectures).
-/
inductive Int : Type where
  /-- A natural number is an integer (`0` to `∞`). -/
  | ofNat   : Nat → Int
  /-- The negation of the successor of a natural number is an integer
    (`-1` to `-∞`). -/
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

/-- Negation of a natural number. -/
def negOfNat : Nat → Int
  | 0      => 0
  | succ m => negSucc m

set_option bootstrap.genMatcherCode false in
/-- Negation of an integer.

  Implemented by efficient native code. -/
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

/-- Subtraction of two natural numbers. -/
def subNatNat (m n : Nat) : Int :=
  match (n - m : Nat) with
  | 0        => ofNat (m - n)  -- m ≥ n
  | (succ k) => negSucc k

set_option bootstrap.genMatcherCode false in
/-- Addition of two integers.

  ```
  #eval (7 : Int) + (6 : Int) -- 13
  #eval (6 : Int) + (-6 : Int) -- 0
  ```

  Implemented by efficient native code. -/
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
/-- Multiplication of two integers.

  ```
  #eval (63 : Int) * (6 : Int) -- 378
  #eval (6 : Int) * (-6 : Int) -- -36
  #eval (7 : Int) * (0 : Int) -- 0
  ```

  Implemented by efficient native code. -/
@[extern "lean_int_mul"]
protected def mul (m n : @& Int) : Int :=
  match m, n with
  | ofNat m, ofNat n => ofNat (m * n)
  | ofNat m, -[n +1] => negOfNat (m * succ n)
  | -[m +1], ofNat n => negOfNat (succ m * n)
  | -[m +1], -[n +1] => ofNat (succ m * succ n)

instance : Mul Int where
  mul := Int.mul

/-- Subtraction of two integers.

  ```
  #eval (63 : Int) - (6 : Int) -- 57
  #eval (7 : Int) - (0 : Int) -- 7
  #eval (0 : Int) - (7 : Int) -- -7
  ```

  Implemented by efficient native code. -/
@[extern "lean_int_sub"]
protected def sub (m n : @& Int) : Int := m + (- n)

instance : Sub Int where
  sub := Int.sub

/-- A proof that an `Int` is non-negative. -/
inductive NonNeg : Int → Prop where
  /-- Sole constructor, proving that `ofNat n` is positive. -/
  | mk (n : Nat) : NonNeg (ofNat n)

/-- Definition of `a ≤ b`, encoded as `b - a ≥ 0`. -/
protected def le (a b : Int) : Prop := NonNeg (b - a)

instance instLEInt : LE Int where
  le := Int.le

/-- Definition of `a < b`, encoded as `a + 1 ≤ b`. -/
protected def lt (a b : Int) : Prop := (a + 1) ≤ b

instance instLTInt : LT Int where
  lt := Int.lt

set_option bootstrap.genMatcherCode false in
/-- Decides equality between two `Int`s.

  ```
  #eval (7 : Int) = (3 : Int) + (4 : Int) -- true
  #eval (6 : Int) = (3 : Int) * (2 : Int) -- true
  #eval ¬ (6 : Int) = (3 : Int) -- true
  ```

  Implemented by efficient native code. -/
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
/-- Absolute value (`Nat`) of an integer.

  ```
  #eval (7 : Int).natAbs -- 7
  #eval (0 : Int).natAbs -- 0
  #eval (-11 : Int).natAbs -- 11
  ```

  Implemented by efficient native code. -/
@[extern "lean_nat_abs"]
def natAbs (m : @& Int) : Nat :=
  match m with
  | ofNat m => m
  | -[m +1] => m.succ

/-! ## sign -/

/--
Returns the "sign" of the integer as another integer: `1` for positive numbers,
`-1` for negative numbers, and `0` for `0`.
-/
def sign : Int → Int
  | Int.ofNat (succ _) => 1
  | Int.ofNat 0 => 0
  | -[_+1]      => -1

/-! ## Conversion -/

/-- Turns an integer into a natural number, negative numbers become
  `0`.

  ```
  #eval (7 : Int).toNat -- 7
  #eval (0 : Int).toNat -- 0
  #eval (-7 : Int).toNat -- 0
  ```
-/
def toNat : Int → Nat
  | ofNat n   => n
  | negSucc _ => 0

/--
* If `n : Nat`, then `int.toNat' n = some n`
* If `n : Int` is negative, then `int.toNat' n = none`.
-/
def toNat' : Int → Option Nat
  | (n : Nat) => some n
  | -[_+1] => none

/-! ## divisibility -/

/--
Divisibility of integers. `a ∣ b` (typed as `\|`) says that
there is some `c` such that `b = a * c`.
-/
instance : Dvd Int where
  dvd a b := Exists (fun c => b = a * c)

/-! ## Powers -/

/-- Power of an integer to some natural number.

  ```
  #eval (2 : Int) ^ 4 -- 16
  #eval (10 : Int) ^ 0 -- 1
  #eval (0 : Int) ^ 10 -- 0
  #eval (-7 : Int) ^ 3 -- -343
  ```
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
The canonical homomorphism `Int → R`.
In most use cases `R` will have a ring structure and this will be a ring homomorphism.
-/
class IntCast (R : Type u) where
  /-- The canonical map `Int → R`. -/
  protected intCast : Int → R

instance : IntCast Int where intCast n := n

/--
Apply the canonical homomorphism from `Int` to a type `R` from an `IntCast R` instance.

In Mathlib there will be such a homomorphism whenever `R` is an additive group with a `1`.
-/
@[coe, reducible, match_pattern] protected def Int.cast {R : Type u} [IntCast R] : Int → R :=
  IntCast.intCast

-- see the notes about coercions into arbitrary types in the module doc-string
instance [IntCast R] : CoeTail Int R where coe := Int.cast

-- see the notes about coercions into arbitrary types in the module doc-string
instance [IntCast R] : CoeHTCT Int R where coe := Int.cast
