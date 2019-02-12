/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

The integers, with addition, multiplication, and subtraction.
-/
prelude
import init.data.nat.basic init.data.list init.coe init.data.repr init.data.to_string
open nat

/- the type, coercions, and notation -/

inductive int : Type
| of_nat : nat → int
| neg_succ_of_nat : nat → int

attribute [extern cpp "lean::nat2int"] int.of_nat
attribute [extern cpp "lean::int_neg_succ_of_nat"] int.neg_succ_of_nat

notation `ℤ` := int

instance : has_coe nat int := ⟨int.of_nat⟩

notation `-[1+ ` n `]` := int.neg_succ_of_nat n

namespace int
protected def zero : int := of_nat 0
protected def one  : int := of_nat 1

instance : has_zero int := ⟨int.zero⟩
instance : has_one int := ⟨int.one⟩

private def nonneg : int → Prop
| (of_nat _) := true
| -[1+ _]    := false

def neg_of_nat : nat → int
| 0        := 0
| (succ m) := -[1+ m]

@[extern cpp "lean::int_neg"]
protected def neg (n : @& int) : int :=
match n with
| (of_nat n) := neg_of_nat n
| -[1+ n]    := succ n

def sub_nat_nat (m n : nat) : int :=
match (n - m : nat) with
| 0        := of_nat (m - n)  -- m ≥ n
| (succ k) := -[1+ k]         -- m < n, and n - m = succ k

@[extern cpp "lean::int_add"]
protected def add (m n : @& int) : int :=
match m, n with
| (of_nat m), (of_nat n) := of_nat (m + n)
| (of_nat m), -[1+ n]    := sub_nat_nat m (succ n)
| -[1+ m],    (of_nat n) := sub_nat_nat n (succ m)
| -[1+ m],    -[1+ n]    := -[1+ succ (m + n)]

@[extern cpp "lean::int_mul"]
protected def mul (m n : @& int) : int :=
match m, n with
| (of_nat m), (of_nat n) := of_nat (m * n)
| (of_nat m), -[1+ n]    := neg_of_nat (m * succ n)
| -[1+ m],    (of_nat n) := neg_of_nat (succ m * n)
| -[1+ m],    -[1+ n]    := of_nat (succ m * succ n)

instance : has_neg int := ⟨int.neg⟩
instance : has_add int := ⟨int.add⟩
instance : has_mul int := ⟨int.mul⟩

@[extern cpp "lean::int_sub"]
protected def sub (m n : @& int) : int :=
m + -n

instance : has_sub int := ⟨int.sub⟩

protected def le (a b : int) : Prop := nonneg (b - a)

instance : has_le int := ⟨int.le⟩

protected def lt (a b : int) : Prop := (a + 1) ≤ b

instance : has_lt int := ⟨int.lt⟩

@[extern cpp "lean::int_dec_eq"]
protected def dec_eq (a b : @& int) : decidable (a = b) :=
match a, b with
 | (of_nat a), (of_nat b) :=
   if h : a = b then is_true (h ▸ rfl)
   else is_false (λ h', int.no_confusion h' (λ h', absurd h' h))
 | (neg_succ_of_nat a), (neg_succ_of_nat b) :=
   if h : a = b then is_true (h ▸ rfl)
   else is_false (λ h', int.no_confusion h' (λ h', absurd h' h))
 | (of_nat a), (int.neg_succ_of_nat b) := is_false (λ h, int.no_confusion h)
 | (neg_succ_of_nat a), (of_nat b) := is_false (λ h, int.no_confusion h)

instance int.decidable_eq : decidable_eq int :=
{dec_eq := int.dec_eq}

@[extern cpp "lean::int_dec_nonneg"]
private def dec_nonneg (m : @& int) : decidable (nonneg m) :=
match m with
| (of_nat m) := show decidable true,  from infer_instance
| -[1+ m]    := show decidable false, from infer_instance

@[extern cpp "lean::int_dec_le"]
instance dec_le (a b : @& int) : decidable (a ≤ b) :=
dec_nonneg _

@[extern cpp "lean::int_dec_lt"]
instance dec_lt (a b : @& int) : decidable (a < b) :=
dec_nonneg _

@[extern cpp "lean::nat_abs"]
def nat_abs (m : @& int) : nat :=
match m with
| (of_nat m)          := m
| (neg_succ_of_nat m) := nat.succ m

protected def repr : int → string
| (of_nat n)          := nat.repr n
| (neg_succ_of_nat n) := "-" ++ nat.repr (succ n)

instance : has_repr int :=
⟨int.repr⟩

instance : has_to_string int :=
⟨int.repr⟩

def sign : int → int
| (n+1:nat) := 1
| 0       := 0
| -[1+ n] := -1

@[extern cpp "lean::int_div"]
def div : (@& int) → (@& int) → int
| (of_nat m) (of_nat n) := of_nat (m / n)
| (of_nat m) -[1+ n]    := -of_nat (m / succ n)
| -[1+ m]    (of_nat n) := -of_nat (succ m / n)
| -[1+ m]    -[1+ n]    := of_nat (succ m / succ n)

@[extern cpp "lean::int_mod"]
def mod : (@& int) → (@& int) → int
| (of_nat m) (of_nat n) := of_nat (m % n)
| (of_nat m) -[1+ n]    := of_nat (m % succ n)
| -[1+ m]    (of_nat n) := -of_nat (succ m % n)
| -[1+ m]    -[1+ n]    := -of_nat (succ m % succ n)

instance : has_div int := ⟨int.div⟩
instance : has_mod int := ⟨int.mod⟩

def to_nat : int → nat
| (n : nat) := n
| -[1+ n] := 0

def nat_mod (m n : int) : nat := (m % n).to_nat

end int
