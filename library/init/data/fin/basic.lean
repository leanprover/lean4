/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.nat.div init.data.nat.bitwise
open nat
structure fin (n : nat) := (val : nat) (isLt : val < n)

attribute [ppUsingAnonymousConstructor] fin

namespace fin

protected def lt {n} (a b : fin n) : Prop :=
a.val < b.val

protected def le {n} (a b : fin n) : Prop :=
a.val ≤ b.val

instance {n} : hasLt (fin n)  := ⟨fin.lt⟩
instance {n} : hasLe (fin n)  := ⟨fin.le⟩

instance decLt {n} (a b : fin n) :  decidable (a < b) :=
nat.decLt _ _

instance decLe {n} (a b : fin n) : decidable (a ≤ b) :=
nat.decLe _ _

def {u} elim0 {α : Sort u} : fin 0 → α
| ⟨_, h⟩ := absurd h (notLtZero _)

variable {n : nat}

def ofNat {n : nat} (a : nat) : fin (succ n) :=
⟨a % succ n, nat.modLt _ (nat.zeroLtSucc _)⟩

private theorem mlt {n b : nat} : ∀ {a}, n > a → b % n < n
| 0     h := nat.modLt _ h
| (a+1) h :=
  have n > 0, from nat.ltTrans (nat.zeroLtSucc _) h,
  nat.modLt _ this

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

instance : hasZero (fin (succ n)) := ⟨⟨0, succPos n⟩⟩
instance : hasOne (fin (succ n))  := ⟨ofNat 1⟩
instance : hasAdd (fin n)         := ⟨fin.add⟩
instance : hasSub (fin n)         := ⟨fin.sub⟩
instance : hasMul (fin n)         := ⟨fin.mul⟩
instance : hasMod (fin n)         := ⟨fin.mod⟩
instance : hasDiv (fin n)         := ⟨fin.div⟩
instance : hasModn (fin n)        := ⟨fin.modn⟩

theorem eqOfVeq : ∀ {i j : fin n}, (val i) = (val j) → i = j
| ⟨iv, ilt₁⟩ ⟨.(iv), ilt₂⟩ rfl := rfl

theorem veqOfEq : ∀ {i j : fin n}, i = j → (val i) = (val j)
| ⟨iv, ilt⟩ .(_) rfl := rfl

theorem neOfVne {i j : fin n} (h : val i ≠ val j) : i ≠ j :=
λ h', absurd (veqOfEq h') h

theorem vneOfNe {i j : fin n} (h : i ≠ j) : val i ≠ val j :=
λ h', absurd (eqOfVeq h') h

theorem modnLt : ∀ {m : nat} (i : fin n), m > 0 → (i %ₙ m).val < m
| m ⟨a, h⟩ hp :=  nat.ltOfLeOfLt (modLe _ _) (modLt _ hp)

end fin

open fin

instance (n : nat) : decidableEq (fin n) :=
{decEq := λ i j, decidableOfDecidableOfIff
  (decEq i.val j.val) ⟨eqOfVeq, veqOfEq⟩}
