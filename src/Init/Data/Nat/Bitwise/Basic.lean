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

theorem shiftLeft_eq (a b : Nat) : a <<< b = a * 2 ^ b :=
  match b with
  | 0 => (Nat.mul_one _).symm
  | b+1 => (shiftLeft_eq _ b).trans <| by
    simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

@[simp] theorem shiftRight_zero : n >>> 0 = n := rfl

theorem shiftRight_succ (m n) : m >>> (n + 1) = (m >>> n) / 2 := rfl

theorem shiftRight_add (m n : Nat) : ∀ k, m >>> (n + k) = (m >>> n) >>> k
  | 0 => rfl
  | k + 1 => by simp [← Nat.add_assoc, shiftRight_add _ _ k, shiftRight_succ]

theorem shiftRight_eq_div_pow (m : Nat) : ∀ n, m >>> n = m / 2 ^ n
  | 0 => (Nat.div_one _).symm
  | k + 1 => by
    rw [shiftRight_add, shiftRight_eq_div_pow m k]
    simp [Nat.div_div_eq_div_mul, ← Nat.pow_succ, shiftRight_succ]

theorem shiftRight_eq_zero (m n : Nat) (hn : m < 2^n) : m >>> n = 0 := by
  simp [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hn]

/-!
### testBit
We define an operation for testing individual bits in the binary representation
of a number.
-/

/-- `testBit m n` returns whether the `(n+1)` least significant bit is `1` or `0`-/
def testBit (m n : Nat) : Bool :=
  -- `1 &&& n` is faster than `n &&& 1` for big `n`.
  1 &&& (m >>> n) != 0

end Nat
