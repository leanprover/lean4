/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

The integers, with addition, multiplication, and subtraction.
-/
prelude
import Init.Data.Nat.Basic
import Init.Data.List
import Init.Data.Repr
import Init.Data.ToString.Basic
open Nat

/- the Type, coercions, and notation -/

inductive Int : Type where
  | ofNat   : Nat → Int
  | negSucc : Nat → Int

attribute [extern "lean_nat_to_int"] Int.ofNat
attribute [extern "lean_int_neg_succ_of_nat"] Int.negSucc

instance : Coe Nat Int := ⟨Int.ofNat⟩

namespace Int
instance : Inhabited Int := ⟨ofNat 0⟩

def negOfNat : Nat → Int
  | 0      => 0
  | succ m => negSucc m

set_option bootstrap.gen_matcher_code false in
@[extern "lean_int_neg"]
protected def neg (n : @& Int) : Int :=
  match n with
  | ofNat n   => negOfNat n
  | negSucc n => succ n

def subNatNat (m n : Nat) : Int :=
  match (n - m : Nat) with
  | 0        => ofNat (m - n)  -- m ≥ n
  | (succ k) => negSucc k

set_option bootstrap.gen_matcher_code false in
@[extern "lean_int_add"]
  protected def add (m n : @& Int) : Int :=
  match m, n with
  | ofNat m,   ofNat n   => ofNat (m + n)
  | ofNat m,   negSucc n => subNatNat m (succ n)
  | negSucc m, ofNat n   => subNatNat n (succ m)
  | negSucc m, negSucc n => negSucc (succ (m + n))

set_option bootstrap.gen_matcher_code false in
@[extern "lean_int_mul"]
protected def mul (m n : @& Int) : Int :=
  match m, n with
  | ofNat m,   ofNat n   => ofNat (m * n)
  | ofNat m,   negSucc n => negOfNat (m * succ n)
  | negSucc m, ofNat n   => negOfNat (succ m * n)
  | negSucc m, negSucc n => ofNat (succ m * succ n)

instance : Neg Int := ⟨Int.neg⟩
instance : Add Int := ⟨Int.add⟩
instance : Mul Int := ⟨Int.mul⟩

@[extern "lean_int_sub"]
protected def sub (m n : @& Int) : Int :=
  m + (- n)

instance : Sub Int := ⟨Int.sub⟩

inductive NonNeg : Int → Prop where
  | mk (n : Nat) : NonNeg (ofNat n)

protected def LessEq (a b : Int) : Prop := NonNeg (b - a)

instance : HasLessEq Int := ⟨Int.LessEq⟩

protected def Less (a b : Int) : Prop := (a + 1) ≤ b

instance : HasLess Int := ⟨Int.Less⟩

set_option bootstrap.gen_matcher_code false in
@[extern "lean_int_dec_eq"]
protected def decEq (a b : @& Int) : Decidable (a = b) :=
  match a, b with
  | ofNat a, ofNat b => match decEq a b with
    | isTrue h  => isTrue  <| h ▸ rfl
    | isFalse h => isFalse <| fun h' => Int.noConfusion h' (fun h' => absurd h' h)
  | negSucc a, negSucc b => match decEq a b with
    | isTrue h  => isTrue  <| h ▸ rfl
    | isFalse h => isFalse <| fun h' => Int.noConfusion h' (fun h' => absurd h' h)
  | ofNat a, negSucc b => isFalse <| fun h => Int.noConfusion h
  | negSucc a, ofNat b => isFalse <| fun h => Int.noConfusion h

instance : DecidableEq Int := Int.decEq

set_option bootstrap.gen_matcher_code false in
@[extern "lean_int_dec_nonneg"]
private def decNonneg (m : @& Int) : Decidable (NonNeg m) :=
  match m with
  | ofNat m   => isTrue <| NonNeg.mk m
  | negSucc m => isFalse <| fun h => nomatch h

@[extern "lean_int_dec_le"]
instance decLe (a b : @& Int) : Decidable (a ≤ b) :=
  decNonneg _

@[extern "lean_int_dec_lt"]
instance decLt (a b : @& Int) : Decidable (a < b) :=
  decNonneg _

set_option bootstrap.gen_matcher_code false in
@[extern "lean_nat_abs"]
def natAbs (m : @& Int) : Nat :=
  match m with
  | ofNat m   => m
  | negSucc m => m.succ

protected def repr : Int → String
  | ofNat m   => Nat.repr m
  | negSucc m => "-" ++ Nat.repr (succ m)

instance : Repr Int := ⟨Int.repr⟩
instance : ToString Int := ⟨Int.repr⟩
instance : OfNat Int n := ⟨Int.ofNat n⟩

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

instance : Div Int := ⟨Int.div⟩
instance : Mod Int := ⟨Int.mod⟩

def toNat : Int → Nat
  | ofNat n   => n
  | negSucc n => 0

def natMod (m n : Int) : Nat := (m % n).toNat

end Int

namespace String

def toInt? (s : String) : Option Int :=
  if s.get 0 = '-' then do
    let v ← (s.toSubstring.drop 1).toNat?;
    pure <| - Int.ofNat v
  else
   Int.ofNat <$> s.toNat?

def isInt (s : String) : Bool :=
  if s.get 0 = '-' then
    (s.toSubstring.drop 1).isNat
  else
    s.isNat

def toInt! (s : String) : Int :=
  match s.toInt? with
  | some v => v
  | none   => panic! "Int expected"

end String
