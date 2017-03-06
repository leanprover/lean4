/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.nat init.data.fin.basic

namespace fin
open nat
variable {n : nat}

def of_nat {n : nat} (a : nat) : fin (succ n) :=
⟨a % succ n, nat.mod_lt _ (nat.zero_lt_succ _)⟩

private lemma mlt {n b : nat} : ∀ {a}, n > a → b % n < n
| 0     h := nat.mod_lt _ h
| (a+1) h :=
  have n > 0, from lt.trans (nat.zero_lt_succ _) h,
  nat.mod_lt _ this

protected def add : fin n → fin n → fin n
| ⟨a, h⟩ ⟨b, _⟩ := ⟨(a + b) % n, mlt h⟩

protected def mul : fin n → fin n → fin n
| ⟨a, h⟩ ⟨b, _⟩ := ⟨(a * b) % n, mlt h⟩

private lemma sublt {a b n : nat} (h : a < n) : a - b < n :=
lt_of_le_of_lt (nat.sub_le a b) h

protected def sub : fin n → fin n → fin n
| ⟨a, h⟩ ⟨b, _⟩ := ⟨a - b, sublt h⟩

private lemma modlt {a b n : nat} (h₁ : a < n) (h₂ : b < n) : a % b < n :=
begin
  cases b with b,
  {simp [mod_zero], assumption},
  {assert h : a % (succ b) < succ b,
   apply nat.mod_lt _ (nat.zero_lt_succ _),
   exact lt.trans h h₂}
end

protected def mod : fin n → fin n → fin n
| ⟨a, h₁⟩ ⟨b, h₂⟩ := ⟨a % b, modlt h₁ h₂⟩

private lemma divlt {a b n : nat} (h : a < n) : a / b < n :=
lt_of_le_of_lt (nat.div_le_self a b) h

protected def div : fin n → fin n → fin n
| ⟨a, h⟩ ⟨b, _⟩ := ⟨a / b, divlt h⟩

protected def lt : fin n → fin n → Prop
| ⟨a, _⟩ ⟨b, _⟩ := a < b

protected def le : fin n → fin n → Prop
| ⟨a, _⟩ ⟨b, _⟩ := a ≤ b

instance : has_zero (fin (succ n)) := ⟨of_nat 0⟩
instance : has_one (fin (succ n))  := ⟨of_nat 1⟩
instance : has_add (fin n)         := ⟨fin.add⟩
instance : has_sub (fin n)         := ⟨fin.sub⟩
instance : has_mul (fin n)         := ⟨fin.mul⟩
instance : has_mod (fin n)         := ⟨fin.mod⟩
instance : has_div (fin n)         := ⟨fin.div⟩
instance : has_lt (fin n)          := ⟨fin.lt⟩
instance : has_le (fin n)          := ⟨fin.le⟩

instance decidable_lt : ∀ (a b : fin n), decidable (a < b)
| ⟨a, _⟩ ⟨b, _⟩ := by apply nat.decidable_lt

instance decidable_le : ∀ (a b : fin n), decidable (a ≤ b)
| ⟨a, _⟩ ⟨b, _⟩ := by apply nat.decidable_le

end fin
