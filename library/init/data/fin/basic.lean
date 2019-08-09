/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.nat.div init.data.nat.bitwise
open Nat
structure Fin (n : Nat) := (val : Nat) (isLt : val < n)

namespace Fin

protected def lt {n} (a b : Fin n) : Prop :=
a.val < b.val

protected def le {n} (a b : Fin n) : Prop :=
a.val ≤ b.val

instance {n} : HasLess (Fin n)    := ⟨Fin.lt⟩
instance {n} : HasLessEq (Fin n)  := ⟨Fin.le⟩

instance decLt {n} (a b : Fin n) :  Decidable (a < b) :=
Nat.decLt _ _

instance decLe {n} (a b : Fin n) : Decidable (a ≤ b) :=
Nat.decLe _ _

def elim0.{u} {α : Sort u} : Fin 0 → α
| ⟨_, h⟩ => absurd h (notLtZero _)

variable {n : Nat}

def ofNat {n : Nat} (a : Nat) : Fin (succ n) :=
⟨a % succ n, Nat.modLt _ (Nat.zeroLtSucc _)⟩

def ofNat' {n : Nat} (a : Nat) (h : n > 0) : Fin n :=
⟨a % n, Nat.modLt _ h⟩

private theorem mlt {n b : Nat} : ∀ {a}, n > a → b % n < n
| 0,   h => Nat.modLt _ h
| a+1, h =>
  have n > 0 from Nat.ltTrans (Nat.zeroLtSucc _) h;
  Nat.modLt _ this

protected def add : Fin n → Fin n → Fin n
| ⟨a, h⟩, ⟨b, _⟩ => ⟨(a + b) % n, mlt h⟩

protected def mul : Fin n → Fin n → Fin n
| ⟨a, h⟩, ⟨b, _⟩ => ⟨(a * b) % n, mlt h⟩

protected def sub : Fin n → Fin n → Fin n
| ⟨a, h⟩, ⟨b, _⟩ => ⟨(a + (n - b)) % n, mlt h⟩

/-
Remark: mod/div/modn/land/lor can be defined without using (% n), but
we are trying to minimize the number of Nat theorems
needed to boostrap Lean.
-/

protected def mod : Fin n → Fin n → Fin n
| ⟨a, h⟩, ⟨b, _⟩ => ⟨(a % b) % n, mlt h⟩

protected def div : Fin n → Fin n → Fin n
| ⟨a, h⟩, ⟨b, _⟩ => ⟨(a / b) % n, mlt h⟩

protected def modn : Fin n → Nat → Fin n
| ⟨a, h⟩, m => ⟨(a % m) % n, mlt h⟩

def land : Fin n → Fin n → Fin n
| ⟨a, h⟩, ⟨b, _⟩ => ⟨(Nat.land a b) % n, mlt h⟩

def lor : Fin n → Fin n → Fin n
| ⟨a, h⟩, ⟨b, _⟩ => ⟨(Nat.lor a b) % n, mlt h⟩

instance : HasZero (Fin (succ n)) := ⟨⟨0, succPos n⟩⟩
instance : HasOne (Fin (succ n))  := ⟨ofNat 1⟩
instance : HasAdd (Fin n)         := ⟨Fin.add⟩
instance : HasSub (Fin n)         := ⟨Fin.sub⟩
instance : HasMul (Fin n)         := ⟨Fin.mul⟩
instance : HasMod (Fin n)         := ⟨Fin.mod⟩
instance : HasDiv (Fin n)         := ⟨Fin.div⟩
instance : HasModn (Fin n)        := ⟨Fin.modn⟩

theorem eqOfVeq : ∀ {i j : Fin n}, (val i) = (val j) → i = j
| ⟨iv, ilt₁⟩, ⟨.(iv), ilt₂⟩, rfl => rfl

theorem veqOfEq : ∀ {i j : Fin n}, i = j → (val i) = (val j)
| ⟨iv, ilt⟩, .(_), rfl => rfl

theorem neOfVne {i j : Fin n} (h : val i ≠ val j) : i ≠ j :=
fun h' => absurd (veqOfEq h') h

theorem vneOfNe {i j : Fin n} (h : i ≠ j) : val i ≠ val j :=
fun h' => absurd (eqOfVeq h') h

theorem modnLt : ∀ {m : Nat} (i : Fin n), m > 0 → (i %ₙ m).val < m
| m, ⟨a, h⟩, hp =>  Nat.ltOfLeOfLt (modLe _ _) (modLt _ hp)

end Fin

open Fin

instance (n : Nat) : DecidableEq (Fin n) :=
{decEq := fun i j => decidableOfDecidableOfIff
  (decEq i.val j.val) ⟨eqOfVeq, veqOfEq⟩}
