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
| ofNat : Nat → Int
| negSuccOfNat : Nat → Int

attribute [extern cpp "lean::nat2int"] Int.ofNat
attribute [extern cpp "lean::int_neg_succ_of_nat"] Int.negSuccOfNat

notation `ℤ` := Int

instance : HasCoe Nat Int := ⟨Int.ofNat⟩

notation `-[1+ ` n `]` := Int.negSuccOfNat n

namespace Int
protected def zero : Int := ofNat 0
protected def one  : Int := ofNat 1

instance : HasZero Int := ⟨Int.zero⟩
instance : HasOne Int := ⟨Int.one⟩

private def nonneg : Int → Prop
| (ofNat _) := True
| -[1+ _]    := False

def negOfNat : Nat → Int
| 0        := 0
| (succ m) := -[1+ m]

@[extern cpp "lean::int_neg"]
protected def neg (n : @& Int) : Int :=
match n with
| (ofNat n) := negOfNat n
| -[1+ n]    := succ n

def subNatNat (m n : Nat) : Int :=
match (n - m : Nat) with
| 0        := ofNat (m - n)  -- m ≥ n
| (succ k) := -[1+ k]         -- m < n, and n - m = succ k

@[extern cpp "lean::int_add"]
protected def add (m n : @& Int) : Int :=
match m, n with
| (ofNat m), (ofNat n) := ofNat (m + n)
| (ofNat m), -[1+ n]    := subNatNat m (succ n)
| -[1+ m],    (ofNat n) := subNatNat n (succ m)
| -[1+ m],    -[1+ n]    := -[1+ succ (m + n)]

@[extern cpp "lean::int_mul"]
protected def mul (m n : @& Int) : Int :=
match m, n with
| (ofNat m), (ofNat n) := ofNat (m * n)
| (ofNat m), -[1+ n]    := negOfNat (m * succ n)
| -[1+ m],    (ofNat n) := negOfNat (succ m * n)
| -[1+ m],    -[1+ n]    := ofNat (succ m * succ n)

instance : HasNeg Int := ⟨Int.neg⟩
instance : HasAdd Int := ⟨Int.add⟩
instance : HasMul Int := ⟨Int.mul⟩

@[extern cpp "lean::int_sub"]
protected def sub (m n : @& Int) : Int :=
m + -n

instance : HasSub Int := ⟨Int.sub⟩

protected def le (a b : Int) : Prop := nonneg (b - a)

instance : HasLe Int := ⟨Int.le⟩

protected def lt (a b : Int) : Prop := (a + 1) ≤ b

instance : HasLt Int := ⟨Int.lt⟩

@[extern cpp "lean::int_dec_eq"]
protected def decEq (a b : @& Int) : Decidable (a = b) :=
match a, b with
 | (ofNat a), (ofNat b) :=
   if h : a = b then isTrue (h ▸ rfl)
   else isFalse (λ h', Int.noConfusion h' (λ h', absurd h' h))
 | (negSuccOfNat a), (negSuccOfNat b) :=
   if h : a = b then isTrue (h ▸ rfl)
   else isFalse (λ h', Int.noConfusion h' (λ h', absurd h' h))
 | (ofNat a), (Int.negSuccOfNat b) := isFalse (λ h, Int.noConfusion h)
 | (negSuccOfNat a), (ofNat b) := isFalse (λ h, Int.noConfusion h)

instance Int.DecidableEq : DecidableEq Int :=
{decEq := Int.decEq}

@[extern cpp "lean::int_dec_nonneg"]
private def decNonneg (m : @& Int) : Decidable (nonneg m) :=
match m with
| (ofNat m) := show Decidable True,  from inferInstance
| -[1+ m]    := show Decidable False, from inferInstance

@[extern cpp "lean::int_dec_le"]
instance decLe (a b : @& Int) : Decidable (a ≤ b) :=
decNonneg _

@[extern cpp "lean::int_dec_lt"]
instance decLt (a b : @& Int) : Decidable (a < b) :=
decNonneg _

@[extern cpp "lean::nat_abs"]
def natAbs (m : @& Int) : Nat :=
match m with
| (ofNat m)          := m
| (negSuccOfNat m) := Nat.succ m

protected def repr : Int → String
| (ofNat n)          := Nat.repr n
| (negSuccOfNat n) := "-" ++ Nat.repr (succ n)

instance : HasRepr Int :=
⟨Int.repr⟩

instance : HasToString Int :=
⟨Int.repr⟩

def sign : Int → Int
| (n+1:Nat) := 1
| 0       := 0
| -[1+ n] := -1

@[extern cpp "lean::int_div"]
def div : (@& Int) → (@& Int) → Int
| (ofNat m) (ofNat n) := ofNat (m / n)
| (ofNat m) -[1+ n]    := -ofNat (m / succ n)
| -[1+ m]    (ofNat n) := -ofNat (succ m / n)
| -[1+ m]    -[1+ n]    := ofNat (succ m / succ n)

@[extern cpp "lean::int_mod"]
def mod : (@& Int) → (@& Int) → Int
| (ofNat m) (ofNat n) := ofNat (m % n)
| (ofNat m) -[1+ n]    := ofNat (m % succ n)
| -[1+ m]    (ofNat n) := -ofNat (succ m % n)
| -[1+ m]    -[1+ n]    := -ofNat (succ m % succ n)

instance : HasDiv Int := ⟨Int.div⟩
instance : HasMod Int := ⟨Int.mod⟩

def toNat : Int → Nat
| (n : Nat) := n
| -[1+ n] := 0

def natMod (m n : Int) : Nat := (m % n).toNat

end Int

namespace String

def toInt (s : String) : Int :=
if s.get 0 = '-' then
 - Int.ofNat (s.foldl (λ n c, n*10 + (c.toNat - '0'.toNat)) 0 1)
else
 Int.ofNat s.toNat

def isInt (s : String) : Bool :=
if s.get 0 = '-' then
  s.all (λ c, c.isDigit) 1
else
  s.isNat

end String
