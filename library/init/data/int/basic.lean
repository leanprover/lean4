/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

The integers, with addition, multiplication, and subtraction.
-/
prelude
import init.data.nat.basic init.data.list init.coe init.data.repr init.data.toString
open nat

/- the type, coercions, and notation -/

inductive int : Type
| ofNat : nat → int
| negSuccOfNat : nat → int

attribute [extern cpp "lean::nat2int"] int.ofNat
attribute [extern cpp "lean::int_neg_succ_of_nat"] int.negSuccOfNat

notation `ℤ` := int

instance : hasCoe nat int := ⟨int.ofNat⟩

notation `-[1+ ` n `]` := int.negSuccOfNat n

namespace int
protected def zero : int := ofNat 0
protected def one  : int := ofNat 1

instance : hasZero int := ⟨int.zero⟩
instance : hasOne int := ⟨int.one⟩

private def nonneg : int → Prop
| (ofNat _) := true
| -[1+ _]    := false

def negOfNat : nat → int
| 0        := 0
| (succ m) := -[1+ m]

@[extern cpp "lean::int_neg"]
protected def neg (n : @& int) : int :=
match n with
| (ofNat n) := negOfNat n
| -[1+ n]    := succ n

def subNatNat (m n : nat) : int :=
match (n - m : nat) with
| 0        := ofNat (m - n)  -- m ≥ n
| (succ k) := -[1+ k]         -- m < n, and n - m = succ k

@[extern cpp "lean::int_add"]
protected def add (m n : @& int) : int :=
match m, n with
| (ofNat m), (ofNat n) := ofNat (m + n)
| (ofNat m), -[1+ n]    := subNatNat m (succ n)
| -[1+ m],    (ofNat n) := subNatNat n (succ m)
| -[1+ m],    -[1+ n]    := -[1+ succ (m + n)]

@[extern cpp "lean::int_mul"]
protected def mul (m n : @& int) : int :=
match m, n with
| (ofNat m), (ofNat n) := ofNat (m * n)
| (ofNat m), -[1+ n]    := negOfNat (m * succ n)
| -[1+ m],    (ofNat n) := negOfNat (succ m * n)
| -[1+ m],    -[1+ n]    := ofNat (succ m * succ n)

instance : hasNeg int := ⟨int.neg⟩
instance : hasAdd int := ⟨int.add⟩
instance : hasMul int := ⟨int.mul⟩

@[extern cpp "lean::int_sub"]
protected def sub (m n : @& int) : int :=
m + -n

instance : hasSub int := ⟨int.sub⟩

protected def le (a b : int) : Prop := nonneg (b - a)

instance : hasLe int := ⟨int.le⟩

protected def lt (a b : int) : Prop := (a + 1) ≤ b

instance : hasLt int := ⟨int.lt⟩

@[extern cpp "lean::int_dec_eq"]
protected def decEq (a b : @& int) : decidable (a = b) :=
match a, b with
 | (ofNat a), (ofNat b) :=
   if h : a = b then isTrue (h ▸ rfl)
   else isFalse (λ h', int.noConfusion h' (λ h', absurd h' h))
 | (negSuccOfNat a), (negSuccOfNat b) :=
   if h : a = b then isTrue (h ▸ rfl)
   else isFalse (λ h', int.noConfusion h' (λ h', absurd h' h))
 | (ofNat a), (int.negSuccOfNat b) := isFalse (λ h, int.noConfusion h)
 | (negSuccOfNat a), (ofNat b) := isFalse (λ h, int.noConfusion h)

instance int.decidableEq : decidableEq int :=
{decEq := int.decEq}

@[extern cpp "lean::int_dec_nonneg"]
private def decNonneg (m : @& int) : decidable (nonneg m) :=
match m with
| (ofNat m) := show decidable true,  from inferInstance
| -[1+ m]    := show decidable false, from inferInstance

@[extern cpp "lean::int_dec_le"]
instance decLe (a b : @& int) : decidable (a ≤ b) :=
decNonneg _

@[extern cpp "lean::int_dec_lt"]
instance decLt (a b : @& int) : decidable (a < b) :=
decNonneg _

@[extern cpp "lean::nat_abs"]
def natAbs (m : @& int) : nat :=
match m with
| (ofNat m)          := m
| (negSuccOfNat m) := nat.succ m

protected def repr : int → string
| (ofNat n)          := nat.repr n
| (negSuccOfNat n) := "-" ++ nat.repr (succ n)

instance : hasRepr int :=
⟨int.repr⟩

instance : hasToString int :=
⟨int.repr⟩

def sign : int → int
| (n+1:nat) := 1
| 0       := 0
| -[1+ n] := -1

@[extern cpp "lean::int_div"]
def div : (@& int) → (@& int) → int
| (ofNat m) (ofNat n) := ofNat (m / n)
| (ofNat m) -[1+ n]    := -ofNat (m / succ n)
| -[1+ m]    (ofNat n) := -ofNat (succ m / n)
| -[1+ m]    -[1+ n]    := ofNat (succ m / succ n)

@[extern cpp "lean::int_mod"]
def mod : (@& int) → (@& int) → int
| (ofNat m) (ofNat n) := ofNat (m % n)
| (ofNat m) -[1+ n]    := ofNat (m % succ n)
| -[1+ m]    (ofNat n) := -ofNat (succ m % n)
| -[1+ m]    -[1+ n]    := -ofNat (succ m % succ n)

instance : hasDiv int := ⟨int.div⟩
instance : hasMod int := ⟨int.mod⟩

def toNat : int → nat
| (n : nat) := n
| -[1+ n] := 0

def natMod (m n : int) : nat := (m % n).toNat

end int
