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

@[extern "lean_int_div"]
def div : (@& Int) → (@& Int) → Int
  | ofNat m,   ofNat n   => ofNat (m / n)
  | ofNat m,   negSucc n => -ofNat (m / succ n)
  | negSucc m, ofNat n   => -ofNat (succ m / n)
  | negSucc m, negSucc n => ofNat (succ m / succ n)

@[extern "lean_int_mod"]
def mod : (@& Int) → (@& Int) → Int
  | ofNat m,   ofNat n   => ofNat (m % n)
  | ofNat m,   negSucc n => ofNat (m % succ n)
  | negSucc m, ofNat n   => -ofNat (succ m % n)
  | negSucc m, negSucc n => -ofNat (succ m % succ n)

instance : Div Int where
  div := Int.div

instance : Mod Int where
  mod := Int.mod

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
