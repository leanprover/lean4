/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Robert Y. Lewis, Keeley Hoek, Mario Carneiro
-/
prelude
import Init.Data.Nat.Bitwise.Basic

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
Remark: land/lor can be defined without using (% n), but
we are trying to minimize the number of Nat theorems
needed to bootstrap Lean.
-/

protected def mod : Fin n → Fin n → Fin n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨a % b,  Nat.lt_of_le_of_lt (Nat.mod_le _ _) h⟩

protected def div : Fin n → Fin n → Fin n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨a / b, Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h⟩

def modn : Fin n → Nat → Fin n
  | ⟨a, h⟩, m => ⟨a % m, Nat.lt_of_le_of_lt (Nat.mod_le _ _) h⟩

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

instance instOfNat : OfNat (Fin (no_index (n+1))) i where
  ofNat := Fin.ofNat i

instance : Inhabited (Fin (no_index (n+1))) where
  default := 0

@[simp] theorem zero_eta : (⟨0, Nat.zero_lt_succ _⟩ : Fin (n + 1)) = 0 := rfl

theorem val_ne_of_ne {i j : Fin n} (h : i ≠ j) : val i ≠ val j :=
  fun h' => absurd (eq_of_val_eq h') h

theorem modn_lt : ∀ {m : Nat} (i : Fin n), m > 0 → (modn i m).val < m
  | _, ⟨_, _⟩, hp =>  by simp [modn]; apply Nat.mod_lt; assumption

theorem val_lt_of_le (i : Fin b) (h : b ≤ n) : i.val < n :=
  Nat.lt_of_lt_of_le i.isLt h

protected theorem pos (i : Fin n) : 0 < n :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) i.2

/-- The greatest value of `Fin (n+1)`. -/
@[inline] def last (n : Nat) : Fin (n + 1) := ⟨n, n.lt_succ_self⟩

/-- `castLT i h` embeds `i` into a `Fin` where `h` proves it belongs into.  -/
@[inline] def castLT (i : Fin m) (h : i.1 < n) : Fin n := ⟨i.1, h⟩

/-- `castLE h i` embeds `i` into a larger `Fin` type.  -/
@[inline] def castLE (h : n ≤ m) (i : Fin n) : Fin m := ⟨i, Nat.lt_of_lt_of_le i.2 h⟩

/-- `cast eq i` embeds `i` into an equal `Fin` type. -/
@[inline] def cast (eq : n = m) (i : Fin n) : Fin m := ⟨i, eq ▸ i.2⟩

/-- `castAdd m i` embeds `i : Fin n` in `Fin (n+m)`. See also `Fin.natAdd` and `Fin.addNat`. -/
@[inline] def castAdd (m) : Fin n → Fin (n + m) :=
  castLE <| Nat.le_add_right n m

/-- `castSucc i` embeds `i : Fin n` in `Fin (n+1)`. -/
@[inline] def castSucc : Fin n → Fin (n + 1) := castAdd 1

/-- `addNat m i` adds `m` to `i`, generalizes `Fin.succ`. -/
def addNat (i : Fin n) (m) : Fin (n + m) := ⟨i + m, Nat.add_lt_add_right i.2 _⟩

/-- `natAdd n i` adds `n` to `i` "on the left". -/
def natAdd (n) (i : Fin m) : Fin (n + m) := ⟨n + i, Nat.add_lt_add_left i.2 _⟩

/-- Maps `0` to `n-1`, `1` to `n-2`, ..., `n-1` to `0`. -/
@[inline] def rev (i : Fin n) : Fin n := ⟨n - (i + 1), Nat.sub_lt i.pos (Nat.succ_pos _)⟩

/-- `subNat i h` subtracts `m` from `i`, generalizes `Fin.pred`. -/
@[inline] def subNat (m) (i : Fin (n + m)) (h : m ≤ i) : Fin n :=
  ⟨i - m, Nat.sub_lt_right_of_lt_add h i.2⟩

/-- Predecessor of a nonzero element of `Fin (n+1)`. -/
@[inline] def pred {n : Nat} (i : Fin (n + 1)) (h : i ≠ 0) : Fin n :=
  subNat 1 i <| Nat.pos_of_ne_zero <| mt (Fin.eq_of_val_eq (j := 0)) h

theorem val_inj {a b : Fin n} : a.1 = b.1 ↔ a = b := ⟨Fin.eq_of_val_eq, Fin.val_eq_of_eq⟩

theorem val_congr {n : Nat} {a b : Fin n} (h : a = b) : (a : Nat) = (b : Nat) :=
  Fin.val_inj.mpr h

theorem val_le_of_le {n : Nat} {a b : Fin n} (h : a ≤ b) : (a : Nat) ≤ (b : Nat) := h

theorem val_le_of_ge {n : Nat} {a b : Fin n} (h : a ≥ b) : (b : Nat) ≤ (a : Nat) := h

theorem val_add_one_le_of_lt {n : Nat} {a b : Fin n} (h : a < b) : (a : Nat) + 1 ≤ (b : Nat) := h

theorem val_add_one_le_of_gt {n : Nat} {a b : Fin n} (h : a > b) : (b : Nat) + 1 ≤ (a : Nat) := h

end Fin
