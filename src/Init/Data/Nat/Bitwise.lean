/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Nat.Basic
import Init.Data.Nat.Div
import Init.Coe

namespace Nat

theorem bitwise_rec_lemma {n : Nat} (hNe : n ≠ 0) : n / 2 < n :=
  Nat.div_lt_self (Nat.zero_lt_of_ne_zero hNe) (Nat.lt_succ_self _)

def bitwise (f : Bool → Bool → Bool) (n m : Nat) : Nat :=
  if n = 0 then
    if f false true then m else 0
  else if m = 0 then
    if f true false then n else 0
  else
    let n' := n / 2
    let m' := m / 2
    let b₁ := n % 2 = 1
    let b₂ := m % 2 = 1
    let r  := bitwise f n' m'
    if f b₁ b₂ then
      r+r+1
    else
      r+r
decreasing_by apply bitwise_rec_lemma; assumption

@[extern "lean_nat_land"]
def land : @& Nat → @& Nat → Nat := bitwise and
@[extern "lean_nat_lor"]
def lor  : @& Nat → @& Nat → Nat := bitwise or
@[extern "lean_nat_lxor"]
def xor  : @& Nat → @& Nat → Nat := bitwise bne
@[extern "lean_nat_shiftl"]
def shiftLeft : @& Nat → @& Nat → Nat
  | n, 0 => n
  | n, succ m => shiftLeft (2*n) m
@[extern "lean_nat_shiftr"]
def shiftRight : @& Nat → @& Nat → Nat
  | n, 0 => n
  | n, succ m => shiftRight n m / 2

instance : AndOp Nat := ⟨Nat.land⟩
instance : OrOp Nat := ⟨Nat.lor⟩
instance : Xor Nat := ⟨Nat.xor⟩
instance : ShiftLeft Nat := ⟨Nat.shiftLeft⟩
instance : ShiftRight Nat := ⟨Nat.shiftRight⟩

end Nat
