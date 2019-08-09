/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

The integers, with addition, multiplication, and subtraction.
-/
prelude
import init.data.nat.basic init.data.list init.coe init.data.repr init.data.tostring
open Nat

/- the Type, coercions, and notation -/

inductive Int : Type
| ofNat   : Nat → Int
| negSucc : Nat → Int

attribute [extern cpp "lean::nat2int"] Int.ofNat
attribute [extern cpp "lean::int_neg_succ_of_nat"] Int.negSucc

instance : HasCoe Nat Int := ⟨Int.ofNat⟩

namespace Int
protected def zero : Int := ofNat 0
protected def one  : Int := ofNat 1

instance : HasZero Int := ⟨Int.zero⟩
instance : HasOne Int  := ⟨Int.one⟩

def negOfNat : Nat → Int
| 0        => 0
| succ m   => negSucc m

@[extern cpp "lean::int_neg"]
protected def neg (n : @& Int) : Int :=
match n with
| ofNat n   => negOfNat n
| negSucc n => succ n

def subNatNat (m n : Nat) : Int :=
match (n - m : Nat) with
| 0        => ofNat (m - n)  -- m ≥ n
| (succ k) => negSucc k

@[extern cpp "lean::int_add"]
protected def add (m n : @& Int) : Int :=
match m, n with
| ofNat m,   ofNat n   => ofNat (m + n)
| ofNat m,   negSucc n => subNatNat m (succ n)
| negSucc m, ofNat n   => subNatNat n (succ m)
| negSucc m, negSucc n => negSucc (m + n)

@[extern cpp "lean::int_mul"]
protected def mul (m n : @& Int) : Int :=
match m, n with
| ofNat m,   ofNat n   => ofNat (m * n)
| ofNat m,   negSucc n => negOfNat (m * succ n)
| negSucc m, ofNat n   => negOfNat (succ m * n)
| negSucc m, negSucc n => ofNat (succ m * succ n)

instance : HasNeg Int := ⟨Int.neg⟩
instance : HasAdd Int := ⟨Int.add⟩
instance : HasMul Int := ⟨Int.mul⟩

@[extern cpp "lean::int_sub"]
protected def sub (m n : @& Int) : Int :=
m + -n

instance : HasSub Int := ⟨Int.sub⟩

inductive NonNeg : Int → Prop
| mk (n : Nat) : NonNeg (ofNat n)

protected def LessEq (a b : Int) : Prop := NonNeg (b - a)

instance : HasLessEq Int := ⟨Int.LessEq⟩

protected def Less (a b : Int) : Prop := (a + 1) ≤ b

instance : HasLess Int := ⟨Int.Less⟩

@[extern cpp "lean::int_dec_eq"]
protected def decEq (a b : @& Int) : Decidable (a = b) :=
match a, b with
 | ofNat a, ofNat b => match decEq a b with
   | isTrue h  => isTrue  $ h ▸ rfl
   | isFalse h => isFalse $ fun h' => Int.noConfusion h' (fun h' => absurd h' h)
 | negSucc a, negSucc b => match decEq a b with
   | isTrue h  => isTrue  $ h ▸ rfl
   | isFalse h => isFalse $ fun h' => Int.noConfusion h' (fun h' => absurd h' h)
 | ofNat a, negSucc b => isFalse $ fun h => Int.noConfusion h
 | negSucc a, ofNat b => isFalse $ fun h => Int.noConfusion h

instance Int.DecidableEq : DecidableEq Int :=
{decEq := Int.decEq}

@[extern cpp "lean::int_dec_nonneg"]
private def decNonneg (m : @& Int) : Decidable (NonNeg m) :=
match m with
| ofNat m   => isTrue $ NonNeg.mk m
| negSucc m => isFalse $ fun h => nomatch h

@[extern cpp "lean::int_dec_le"]
instance decLe (a b : @& Int) : Decidable (a ≤ b) :=
decNonneg _

@[extern cpp "lean::int_dec_lt"]
instance decLt (a b : @& Int) : Decidable (a < b) :=
decNonneg _

@[extern cpp "lean::nat_abs"]
def natAbs (m : @& Int) : Nat :=
match m with
| ofNat m   => m
| negSucc m => m.succ

protected def repr : Int → String
| ofNat m     => Nat.repr m
| negSucc m   => "-" ++ Nat.repr (succ m)

instance : HasRepr Int :=
⟨Int.repr⟩

instance : HasToString Int :=
⟨Int.repr⟩

@[extern cpp "lean::int_div"]
def div : (@& Int) → (@& Int) → Int
| ofNat m,     ofNat n     => ofNat (m / n)
| ofNat m,     negSucc n   => -ofNat (m / succ n)
| negSucc m,   ofNat n     => -ofNat (succ m / n)
| negSucc m,   negSucc n   => ofNat (succ m / succ n)

@[extern cpp "lean::int_mod"]
def mod : (@& Int) → (@& Int) → Int
| ofNat m,     ofNat n     => ofNat (m % n)
| ofNat m,     negSucc n   => ofNat (m % succ n)
| negSucc m,   ofNat n     => -ofNat (succ m % n)
| negSucc m,   negSucc n   => -ofNat (succ m % succ n)

instance : HasDiv Int := ⟨Int.div⟩
instance : HasMod Int := ⟨Int.mod⟩

def toNat : Int → Nat
| ofNat n     => n
| negSucc n   => 0

def natMod (m n : Int) : Nat := (m % n).toNat

end Int

namespace String

def toInt (s : String) : Int :=
if s.get 0 = '-' then
 - Int.ofNat (s.toSubstring.drop 1).toNat
else
 Int.ofNat s.toNat

def isInt (s : String) : Bool :=
if s.get 0 = '-' then
  (s.toSubstring.drop 1).isNat
else
  s.isNat

end String
