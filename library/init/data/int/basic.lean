/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

The integers, with addition, multiplication, and subtraction.
-/
prelude
import init.data.nat.basic init.data.list init.coe init.data.repr init.data.to_string
open nat

/- the type, coercions, and notation -/

inductive int : Type
| of_nat : nat → int
| neg_succ_of_nat : nat → int

notation `ℤ` := int

instance : has_coe nat int := ⟨int.of_nat⟩

notation `-[1+ ` n `]` := int.neg_succ_of_nat n

def int.nat_abs : int → nat
| (int.of_nat m)          := m
| (int.neg_succ_of_nat m) := nat.succ m

instance : decidable_eq int :=
{dec_eq := λ a b, match a, b with
 | (int.of_nat a), (int.of_nat b) :=
   if h : a = b then is_true (h ▸ rfl)
   else is_false (λ h', int.no_confusion h' (λ h', absurd h' h))
 | (int.neg_succ_of_nat a), (int.neg_succ_of_nat b) :=
   if h : a = b then is_true (h ▸ rfl)
   else is_false (λ h', int.no_confusion h' (λ h', absurd h' h))
 | (int.of_nat a), (int.neg_succ_of_nat b) := is_false (λ h, int.no_confusion h)
 | (int.neg_succ_of_nat a), (int.of_nat b) := is_false (λ h, int.no_confusion h)}

protected def int.repr : int → string
| (int.of_nat n)          := repr n
| (int.neg_succ_of_nat n) := "-" ++ repr (succ n)

instance : has_repr int :=
⟨int.repr⟩

instance : has_to_string int :=
⟨int.repr⟩

namespace int

protected def zero : int := of_nat 0
protected def one  : int := of_nat 1

instance : has_zero int := ⟨int.zero⟩
instance : has_one int := ⟨int.one⟩

def neg_of_nat : ℕ → int
| 0        := 0
| (succ m) := -[1+ m]

def sub_nat_nat (m n : ℕ) : int :=
match (n - m : nat) with
| 0        := of_nat (m - n)  -- m ≥ n
| (succ k) := -[1+ k]         -- m < n, and n - m = succ k

protected def neg : int → int
| (of_nat n) := neg_of_nat n
| -[1+ n]    := succ n

protected def add : int → int → int
| (of_nat m) (of_nat n) := of_nat (m + n)
| (of_nat m) -[1+ n]    := sub_nat_nat m (succ n)
| -[1+ m]    (of_nat n) := sub_nat_nat n (succ m)
| -[1+ m]    -[1+ n]    := -[1+ succ (m + n)]

protected def mul : int → int → int
| (of_nat m) (of_nat n) := of_nat (m * n)
| (of_nat m) -[1+ n]    := neg_of_nat (m * succ n)
| -[1+ m]    (of_nat n) := neg_of_nat (succ m * n)
| -[1+ m]    -[1+ n]    := of_nat (succ m * succ n)

instance : has_neg int := ⟨int.neg⟩
instance : has_add int := ⟨int.add⟩
instance : has_mul int := ⟨int.mul⟩

protected def sub (m n : int) : int :=
m + -n

instance : has_sub int := ⟨int.sub⟩

def sign : int → int
| (n+1:ℕ) := 1
| 0       := 0
| -[1+ n] := -1

protected def div : int → int → int
| (m : ℕ) (n : ℕ) := of_nat (m / n)
| (m : ℕ) -[1+ n] := -of_nat (m / succ n)
| -[1+ m] 0       := 0
| -[1+ m] (n+1:ℕ) := -[1+ m / succ n]
| -[1+ m] -[1+ n] := of_nat (succ (m / succ n))

protected def mod : int → int → int
| (m : ℕ) n := (m % nat_abs n : ℕ)
| -[1+ m] n := sub_nat_nat (nat_abs n) (succ (m % nat_abs n))

-- F-rounding: This pair satisfies fdiv x y = floor (x / y)
def fdiv : int → int → int
| 0       _       := 0
| (m : ℕ) (n : ℕ) := of_nat (m / n)
| (m+1:ℕ) -[1+ n] := -[1+ m / succ n]
| -[1+ m] 0       := 0
| -[1+ m] (n+1:ℕ) := -[1+ m / succ n]
| -[1+ m] -[1+ n] := of_nat (succ m / succ n)

def fmod : int → int → int
| 0       _       := 0
| (m : ℕ) (n : ℕ) := of_nat (m % n)
| (m+1:ℕ) -[1+ n] := sub_nat_nat (m % succ n) n
| -[1+ m] (n : ℕ) := sub_nat_nat n (succ (m % n))
| -[1+ m] -[1+ n] := -of_nat (succ m % succ n)

-- T-rounding: This pair satisfies quot x y = round_to_zero (x / y)
def quot : int → int → int
| (of_nat m) (of_nat n) := of_nat (m / n)
| (of_nat m) -[1+ n]    := -of_nat (m / succ n)
| -[1+ m]    (of_nat n) := -of_nat (succ m / n)
| -[1+ m]    -[1+ n]    := of_nat (succ m / succ n)

def rem : int → int → int
| (of_nat m) (of_nat n) := of_nat (m % n)
| (of_nat m) -[1+ n]    := of_nat (m % succ n)
| -[1+ m]    (of_nat n) := -of_nat (succ m % n)
| -[1+ m]    -[1+ n]    := -of_nat (succ m % succ n)

instance : has_div int := ⟨int.div⟩
instance : has_mod int := ⟨int.mod⟩

def to_nat : int → ℕ
| (n : ℕ) := n
| -[1+ n] := 0

def nat_mod (m n : int) : ℕ := (m % n).to_nat

private def nonneg : int → Prop
| (of_nat _) := true
| -[1+ _]    := false

protected def le (a b : int) : Prop := nonneg (b - a)

instance : has_le int := ⟨int.le⟩

protected def lt (a b : int) : Prop := (a + 1) ≤ b

instance : has_lt int := ⟨int.lt⟩

private def decidable_nonneg : Π (a : int), decidable (nonneg a)
| (of_nat m) := show decidable true,  from infer_instance
| -[1+ m]    := show decidable false, from infer_instance

instance decidable_le (a b : int) : decidable (a ≤ b) :=
decidable_nonneg _

instance decidable_lt (a b : int) : decidable (a < b) :=
decidable_nonneg _

end int
