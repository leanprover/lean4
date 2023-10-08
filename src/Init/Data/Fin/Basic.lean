/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Data.Nat.Div
import Init.Data.Nat.Bitwise
import Init.Coe

open Nat

namespace Fin

instance coeToNat : CoeOut (Fin n) Nat :=
  ⟨fun v => v.val⟩

def elim0.{u} {α : Sort u} : Fin 0 → α
  | ⟨_, h⟩ => absurd h (not_lt_zero _)

def succ : Fin n → Fin n.succ
  | ⟨i, h⟩ => ⟨i+1, Nat.succ_lt_succ h⟩

variable {n : Nat}

protected def ofNat {n : Nat} (a : Nat) : Fin n.succ :=
  ⟨a % (n+1), Nat.mod_lt _ (Nat.zero_lt_succ _)⟩

protected def ofNat' {n : Nat} (a : Nat) (h : n > 0) : Fin n :=
  ⟨a % n, Nat.mod_lt _ h⟩

private theorem mlt {b : Nat} : {a : Nat} → a < n → b % n < n
  | 0,   h => Nat.mod_lt _ h
  | _+1, h =>
    have : n > 0 := Nat.lt_trans (Nat.zero_lt_succ _) h;
    Nat.mod_lt _ this

protected def add : Fin n → Fin n → Fin n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨(a + b) % n, mlt h⟩

protected def mul : Fin n → Fin n → Fin n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨(a * b) % n, mlt h⟩

protected def sub : Fin n → Fin n → Fin n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨(a + (n - b)) % n, mlt h⟩

/-!
Remark: mod/div/modn/land/lor can be defined without using (% n), but
we are trying to minimize the number of Nat theorems
needed to bootstrap Lean.
-/

protected def mod : Fin n → Fin n → Fin n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨(a % b) % n, mlt h⟩

protected def div : Fin n → Fin n → Fin n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨(a / b) % n, mlt h⟩

def modn : Fin n → Nat → Fin n
  | ⟨a, h⟩, m => ⟨(a % m) % n, mlt h⟩

def land : Fin n → Fin n → Fin n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨(Nat.land a b) % n, mlt h⟩

def lor : Fin n → Fin n → Fin n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨(Nat.lor a b) % n, mlt h⟩

def xor : Fin n → Fin n → Fin n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨(Nat.xor a b) % n, mlt h⟩

def shiftLeft : Fin n → Fin n → Fin n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨(a <<< b) % n, mlt h⟩

def shiftRight : Fin n → Fin n → Fin n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨(a >>> b) % n, mlt h⟩

instance : Add (Fin n) where
  add := Fin.add

instance : Sub (Fin n) where
  sub := Fin.sub

instance : Mul (Fin n) where
  mul := Fin.mul

instance : Mod (Fin n) where
  mod := Fin.mod

instance : Div (Fin n) where
  div := Fin.div

instance : AndOp (Fin n) where
  and := Fin.land
instance : OrOp (Fin n) where
  or := Fin.lor
instance : Xor (Fin n) where
  xor := Fin.xor
instance : ShiftLeft (Fin n) where
  shiftLeft := Fin.shiftLeft
instance : ShiftRight (Fin n) where
  shiftRight := Fin.shiftRight

instance : OfNat (Fin (no_index (n+1))) i where
  ofNat := Fin.ofNat i

instance : Inhabited (Fin (no_index (n+1))) where
  default := 0

theorem val_ne_of_ne {i j : Fin n} (h : i ≠ j) : val i ≠ val j :=
  fun h' => absurd (eq_of_val_eq h') h

theorem modn_lt : ∀ {m : Nat} (i : Fin n), m > 0 → (modn i m).val < m
  | _, ⟨_, _⟩, hp =>  Nat.lt_of_le_of_lt (mod_le _ _) (mod_lt _ hp)

theorem val_lt_of_le (i : Fin b) (h : b ≤ n) : i.val < n :=
  Nat.lt_of_lt_of_le i.isLt h

end Fin

instance [GetElem cont Nat elem dom] : GetElem cont (Fin n) elem fun xs i => dom xs i where
  getElem xs i h := getElem xs i.1 h

macro_rules
  | `(tactic| get_elem_tactic_trivial) => `(tactic| apply Fin.val_lt_of_le; get_elem_tactic_trivial; done)
