/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.nat.div init.data.nat.bitwise
open nat
structure fin (n : nat) := (val : nat) (is_lt : val < n)

attribute [pp_using_anonymous_constructor] fin

namespace fin

protected def lt {n} (a b : fin n) : Prop :=
a.val < b.val

protected def le {n} (a b : fin n) : Prop :=
a.val ≤ b.val

instance {n} : has_lt (fin n)  := ⟨fin.lt⟩
instance {n} : has_le (fin n)  := ⟨fin.le⟩

instance dec_lt {n} (a b : fin n) :  decidable (a < b) :=
nat.dec_lt _ _

instance dec_le {n} (a b : fin n) : decidable (a ≤ b) :=
nat.dec_le _ _

def {u} elim0 {α : Sort u} : fin 0 → α
| ⟨_, h⟩ := absurd h (not_lt_zero _)

variable {n : nat}

def of_nat {n : nat} (a : nat) : fin (succ n) :=
⟨a % succ n, nat.mod_lt _ (nat.zero_lt_succ _)⟩

private theorem mlt {n b : nat} : ∀ {a}, n > a → b % n < n
| 0     h := nat.mod_lt _ h
| (a+1) h :=
  have n > 0, from nat.lt_trans (nat.zero_lt_succ _) h,
  nat.mod_lt _ this

protected def add : fin n → fin n → fin n
| ⟨a, h⟩ ⟨b, _⟩ := ⟨(a + b) % n, mlt h⟩

protected def mul : fin n → fin n → fin n
| ⟨a, h⟩ ⟨b, _⟩ := ⟨(a * b) % n, mlt h⟩

protected def sub : fin n → fin n → fin n
| ⟨a, h⟩ ⟨b, _⟩ := ⟨(a + (n - b)) % n, mlt h⟩

/-
Remark: mod/div/modn/land/lor can be defined without using (% n), but
we are trying to minimize the number of nat theorems
needed to boostrap Lean.
-/

protected def mod : fin n → fin n → fin n
| ⟨a, h⟩ ⟨b, _⟩ := ⟨(a % b) % n, mlt h⟩

protected def div : fin n → fin n → fin n
| ⟨a, h⟩ ⟨b, _⟩ := ⟨(a / b) % n, mlt h⟩

protected def modn : fin n → nat → fin n
| ⟨a, h⟩ m := ⟨(a % m) % n, mlt h⟩

def land : fin n → fin n → fin n
| ⟨a, h⟩ ⟨b, _⟩ := ⟨(nat.land a b) % n, mlt h⟩

def lor : fin n → fin n → fin n
| ⟨a, h⟩ ⟨b, _⟩ := ⟨(nat.lor a b) % n, mlt h⟩

instance : has_zero (fin (succ n)) := ⟨⟨0, succ_pos n⟩⟩
instance : has_one (fin (succ n))  := ⟨of_nat 1⟩
instance : has_add (fin n)         := ⟨fin.add⟩
instance : has_sub (fin n)         := ⟨fin.sub⟩
instance : has_mul (fin n)         := ⟨fin.mul⟩
instance : has_mod (fin n)         := ⟨fin.mod⟩
instance : has_div (fin n)         := ⟨fin.div⟩
instance : has_modn (fin n)        := ⟨fin.modn⟩

theorem eq_of_veq : ∀ {i j : fin n}, (val i) = (val j) → i = j
| ⟨iv, ilt₁⟩ ⟨.(iv), ilt₂⟩ rfl := rfl

theorem veq_of_eq : ∀ {i j : fin n}, i = j → (val i) = (val j)
| ⟨iv, ilt⟩ .(_) rfl := rfl

theorem ne_of_vne {i j : fin n} (h : val i ≠ val j) : i ≠ j :=
λ h', absurd (veq_of_eq h') h

theorem vne_of_ne {i j : fin n} (h : i ≠ j) : val i ≠ val j :=
λ h', absurd (eq_of_veq h') h

theorem modn_lt : ∀ {m : nat} (i : fin n), m > 0 → (i %ₙ m).val < m
| m ⟨a, h⟩ hp :=  nat.lt_of_le_of_lt (mod_le _ _) (mod_lt _ hp)

end fin

open fin

instance (n : nat) : decidable_eq (fin n) :=
{dec_eq := λ i j, decidable_of_decidable_of_iff
  (dec_eq i.val j.val) ⟨eq_of_veq, veq_of_eq⟩}
