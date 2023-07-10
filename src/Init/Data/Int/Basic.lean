/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

The integers, with addition, multiplication, and subtraction.
-/
prelude
import Init.Coe
import Init.Data.Nat.Div
import Init.Data.List.Basic
set_option linter.missingDocs true -- keep it documented
open Nat

/-! # Integer Type, Coercions, and Notation

This file defines the `Int` type as well as

* coercions, conversions, and compatibility with numeric literals,
* basic arithmetic operations add/sub/mul/div/mod/pow,
* a few `Nat`-related operations such as `negOfNat` and `subNatNat`,
* relations `<`/`≤`/`≥`/`>`, the `NonNeg` property and `min`/`max`,
* decidability of equality, relations and `NonNeg`.
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

instance : Coe Nat Int := ⟨Int.ofNat⟩

instance : OfNat Int n where
  ofNat := Int.ofNat n

namespace Int
instance : Inhabited Int := ⟨ofNat 0⟩

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
instance : Neg Int where
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
  | ofNat m,   ofNat n   => ofNat (m + n)
  | ofNat m,   negSucc n => subNatNat m (succ n)
  | negSucc m, ofNat n   => subNatNat n (succ m)
  | negSucc m, negSucc n => negSucc (succ (m + n))

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
  | ofNat m,   ofNat n   => ofNat (m * n)
  | ofNat m,   negSucc n => negOfNat (m * succ n)
  | negSucc m, ofNat n   => negOfNat (succ m * n)
  | negSucc m, negSucc n => ofNat (succ m * succ n)

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
protected def sub (m n : @& Int) : Int :=
  m + (- n)

instance : Sub Int where
  sub := Int.sub

/-- A proof that an `Int` is non-negative. -/
inductive NonNeg : Int → Prop where
  /-- Sole constructor, proving that `ofNat n` is positive. -/
  | mk (n : Nat) : NonNeg (ofNat n)

/-- Definition of `a ≤ b`, encoded as `b - a ≥ 0`. -/
protected def le (a b : Int) : Prop := NonNeg (b - a)

instance : LE Int where
  le := Int.le

/-- Definition of `a < b`, encoded as `a + 1 ≤ b`. -/
protected def lt (a b : Int) : Prop := (a + 1) ≤ b

instance : LT Int where
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
  | negSucc a, negSucc b => match decEq a b with
    | isTrue h  => isTrue  <| h ▸ rfl
    | isFalse h => isFalse <| fun h' => Int.noConfusion h' (fun h' => absurd h' h)
  | ofNat _, negSucc _ => isFalse <| fun h => Int.noConfusion h
  | negSucc _, ofNat _ => isFalse <| fun h => Int.noConfusion h

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
  | ofNat m   => isTrue <| NonNeg.mk m
  | negSucc _ => isFalse <| fun h => nomatch h

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
  | ofNat m   => m
  | negSucc m => m.succ

/-- Integer division. This function uses the
  [*"T-rounding"*][t-rounding] (**T**runcation-rounding) convention,
  meaning that it rounds toward zero. Also note that division by zero
  is defined to equal zero.

  The relation between integer division and modulo is found in [the
  `Int.mod_add_div` theorem in std][theo mod_add_div] which states
  that `a % b + b * (a / b) = a`, unconditionally.

  [t-rounding]: https://dl.acm.org/doi/pdf/10.1145/128861.128862
  [theo mod_add_div]: https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Int.mod_add_div#doc

  Examples:

  ```
  #eval (7 : Int) / (0 : Int) -- 0
  #eval (0 : Int) / (7 : Int) -- 0

  #eval (12 : Int) / (6 : Int) -- 2
  #eval (12 : Int) / (-6 : Int) -- -2
  #eval (-12 : Int) / (6 : Int) -- -2
  #eval (-12 : Int) / (-6 : Int) -- 2

  #eval (12 : Int) / (7 : Int) -- 1
  #eval (12 : Int) / (-7 : Int) -- -1
  #eval (-12 : Int) / (7 : Int) -- -1
  #eval (-12 : Int) / (-7 : Int) -- 1
  ```

  Implemented by efficient native code. -/
@[extern "lean_int_div"]
def div : (@& Int) → (@& Int) → Int
  | ofNat m,   ofNat n   => ofNat (m / n)
  | ofNat m,   negSucc n => -ofNat (m / succ n)
  | negSucc m, ofNat n   => -ofNat (succ m / n)
  | negSucc m, negSucc n => ofNat (succ m / succ n)

instance : Div Int where
  div := Int.div

/-- Integer modulo. This function uses the
  [*"T-rounding"*][t-rounding] (**T**runcation-rounding) convention
  to pair with `Int.div`, meaning that `a % b + b * (a / b) = a`
  unconditionally (see [`Int.mod_add_div`][theo mod_add_div]). In
  particular, `a % 0 = a`.

  [t-rounding]: https://dl.acm.org/doi/pdf/10.1145/128861.128862
  [theo mod_add_div]: https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Int.mod_add_div#doc

  Examples:

  ```
  #eval (7 : Int) % (0 : Int) -- 7
  #eval (0 : Int) % (7 : Int) -- 0

  #eval (12 : Int) % (6 : Int) -- 0
  #eval (12 : Int) % (-6 : Int) -- 0
  #eval (-12 : Int) % (6 : Int) -- 0
  #eval (-12 : Int) % (-6 : Int) -- 0

  #eval (12 : Int) % (7 : Int) -- 5
  #eval (12 : Int) % (-7 : Int) -- 5
  #eval (-12 : Int) % (7 : Int) -- 2
  #eval (-12 : Int) % (-7 : Int) -- 2
  ```

  Implemented by efficient native code. -/
@[extern "lean_int_mod"]
def mod : (@& Int) → (@& Int) → Int
  | ofNat m,   ofNat n   => ofNat (m % n)
  | ofNat m,   negSucc n => ofNat (m % succ n)
  | negSucc m, ofNat n   => -ofNat (succ m % n)
  | negSucc m, negSucc n => -ofNat (succ m % succ n)

instance : Mod Int where
  mod := Int.mod

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

instance : HPow Int Nat Int where
  hPow := Int.pow

instance : LawfulBEq Int where
  eq_of_beq h := by simp [BEq.beq] at h; assumption
  rfl := by simp [BEq.beq]

instance : Min Int := minOfLe

instance : Max Int := maxOfLe

end Int
