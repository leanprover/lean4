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
open Nat

/-! # the Type, coercions, and notation -/

inductive Int : Type where
  | ofNat   : Nat → Int
  | negSucc : Nat → Int

attribute [extern "lean_nat_to_int"] Int.ofNat
attribute [extern "lean_int_neg_succ_of_nat"] Int.negSucc

instance : Coe Nat Int := ⟨Int.ofNat⟩

instance : OfNat Int n where
  ofNat := Int.ofNat n

namespace Int
instance : Inhabited Int := ⟨ofNat 0⟩

def negOfNat : Nat → Int
  | 0      => 0
  | succ m => negSucc m

set_option bootstrap.genMatcherCode false in
@[extern "lean_int_neg"]
protected def neg (n : @& Int) : Int :=
  match n with
  | ofNat n   => negOfNat n
  | negSucc n => succ n

def subNatNat (m n : Nat) : Int :=
  match (n - m : Nat) with
  | 0        => ofNat (m - n)  -- m ≥ n
  | (succ k) => negSucc k

set_option bootstrap.genMatcherCode false in
@[extern "lean_int_add"]
  protected def add (m n : @& Int) : Int :=
  match m, n with
  | ofNat m,   ofNat n   => ofNat (m + n)
  | ofNat m,   negSucc n => subNatNat m (succ n)
  | negSucc m, ofNat n   => subNatNat n (succ m)
  | negSucc m, negSucc n => negSucc (succ (m + n))

set_option bootstrap.genMatcherCode false in
@[extern "lean_int_mul"]
protected def mul (m n : @& Int) : Int :=
  match m, n with
  | ofNat m,   ofNat n   => ofNat (m * n)
  | ofNat m,   negSucc n => negOfNat (m * succ n)
  | negSucc m, ofNat n   => negOfNat (succ m * n)
  | negSucc m, negSucc n => ofNat (succ m * succ n)

/--
  The `Neg Int` default instance must have priority higher than `low` since
  the default instance `OfNat Nat n` has `low` priority.
  ```
  #check -42
  ```
-/
@[default_instance mid]
instance : Neg Int where
  neg := Int.neg
instance : Add Int where
  add := Int.add
instance : Mul Int where
  mul := Int.mul

@[extern "lean_int_sub"]
protected def sub (m n : @& Int) : Int :=
  m + (- n)

instance : Sub Int where
  sub := Int.sub

inductive NonNeg : Int → Prop where
  | mk (n : Nat) : NonNeg (ofNat n)

protected def le (a b : Int) : Prop := NonNeg (b - a)

instance : LE Int where
  le := Int.le

protected def lt (a b : Int) : Prop := (a + 1) ≤ b

instance : LT Int where
  lt := Int.lt

set_option bootstrap.genMatcherCode false in
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
@[extern "lean_int_dec_nonneg"]
private def decNonneg (m : @& Int) : Decidable (NonNeg m) :=
  match m with
  | ofNat m   => isTrue <| NonNeg.mk m
  | negSucc _ => isFalse <| fun h => nomatch h

@[extern "lean_int_dec_le"]
instance decLe (a b : @& Int) : Decidable (a ≤ b) :=
  decNonneg _

@[extern "lean_int_dec_lt"]
instance decLt (a b : @& Int) : Decidable (a < b) :=
  decNonneg _

set_option bootstrap.genMatcherCode false in
@[extern "lean_nat_abs"]
def natAbs (m : @& Int) : Nat :=
  match m with
  | ofNat m   => m
  | negSucc m => m.succ

/--
There are three plausible definitions of the division and modulus operation
on `Int`.

* `Int.ediv`, `Int.emod`: E-rounding (euclidean division):
  satisfies `0 ≤ emod x y < natAbs y` for `y ≠ 0`
* `Int.fdiv`, `Int.fmod`: F-rounding (flooring division):
  satisfies `fdiv x y = floor (x / y)`
* `Int.tdiv`, `Int.tmod`: T-rounding (truncating division):
  satisfies `tdiv x y = round_to_zero (x / y)`

In each case, the pair of functions unconditionally satisfies
`x % y + (x / y) * y = x`
which is used to fix the value of one function based on the other.
All versions also satisfy `x / 0 = 0` and `x % 0 = x`.

Lean 3 used `Int.ediv` and `Int.emod` for the typeclass instances.
Lean 4 is now using `Int.tdiv` and `Int.tmod`,
for compatibility with C conventions.
See https://blog.vero.site/post/modulo for the history of these conventions.

Mathlib4 intends to continue using `Int.ediv` and `Int.emod`,
and to enable that without being prescriptive,
we do not provide instances `Div Int` or `Mod Int` here,
preferring to directly call the functions in the few places they are needed
in Lean 4.
-/
@[extern "lean_int_tdiv"]
def tdiv : (@& Int) → (@& Int) → Int
  | ofNat m,   ofNat n   => ofNat (m / n)
  | ofNat m,   negSucc n => -ofNat (m / succ n)
  | negSucc m, ofNat n   => -ofNat (succ m / n)
  | negSucc m, negSucc n => ofNat (succ m / succ n)

/--
Integer modulus, with truncating division.
See the doc-string for `Int.tdiv` for a detailed explanation.
-/
@[extern "lean_int_tmod"]
def tmod : (@& Int) → (@& Int) → Int
  | ofNat m,   ofNat n   => ofNat (m % n)
  | ofNat m,   negSucc n => ofNat (m % succ n)
  | negSucc m, ofNat n   => -ofNat (succ m % n)
  | negSucc m, negSucc n => -ofNat (succ m % succ n)

def toNat : Int → Nat
  | ofNat n   => n
  | negSucc _ => 0

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
