/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Coe

public section

namespace Nat

theorem bitwise_rec_lemma {n : Nat} (hNe : n ≠ 0) : n / 2 < n :=
  Nat.div_lt_self (Nat.zero_lt_of_ne_zero hNe) (Nat.lt_succ_self _)

/--
A helper for implementing bitwise operators on `Nat`.

Each bit of the resulting `Nat` is the result of applying `f` to the corresponding bits of the input
`Nat`s, up to the position of the highest set bit in either input.
-/
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

/--
Bitwise and. Usually accessed via the `&&&` operator.

Each bit of the resulting value is set if the corresponding bit is set in both of the inputs.
-/
@[extern "lean_nat_land"]
def land : @& Nat → @& Nat → Nat := bitwise and

/--
Bitwise or. Usually accessed via the `|||` operator.

Each bit of the resulting value is set if the corresponding bit is set in at least one of the inputs.
-/
@[extern "lean_nat_lor"]
def lor  : @& Nat → @& Nat → Nat := bitwise or

/--
Bitwise exclusive or. Usually accessed via the `^^^` operator.

Each bit of the resulting value is set if the corresponding bit is set in exactly one of the inputs.
-/
@[extern "lean_nat_lxor"]
def xor  : @& Nat → @& Nat → Nat := bitwise bne

/--
Shifts the binary representation of a value left by the specified number of bits. Usually accessed
via the `<<<` operator.

Examples:
 * `1 <<< 2 = 4`
 * `1 <<< 3 = 8`
 * `0 <<< 3 = 0`
 * `0xf1 <<< 4 = 0xf10`
-/
@[extern "lean_nat_shiftl", expose]
def shiftLeft : @& Nat → @& Nat → Nat
  | n, 0 => n
  | n, succ m => shiftLeft (2*n) m

/--
Shifts the binary representation of a value right by the specified number of bits. Usually accessed
via the `>>>` operator.

Examples:
 * `4 >>> 2 = 1`
 * `8 >>> 2 = 2`
 * `8 >>> 3 = 1`
 * `0 >>> 3 = 0`
 * `0xf13a >>> 8 = 0xf1`
-/
@[extern "lean_nat_shiftr", expose]
def shiftRight : @& Nat → @& Nat → Nat
  | n, 0 => n
  | n, succ m => shiftRight n m / 2

instance : AndOp Nat := ⟨Nat.land⟩
instance : OrOp Nat := ⟨Nat.lor⟩
instance : XorOp Nat := ⟨Nat.xor⟩
instance : ShiftLeft Nat := ⟨Nat.shiftLeft⟩
instance : ShiftRight Nat := ⟨Nat.shiftRight⟩

theorem shiftLeft_eq (a b : Nat) : a <<< b = a * 2 ^ b :=
  match b with
  | 0 => (Nat.mul_one _).symm
  | b+1 => (shiftLeft_eq _ b).trans <| by
    simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm]

@[simp, grind =] theorem shiftRight_zero : n >>> 0 = n := rfl

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

theorem shiftRight_le (m n : Nat) : m >>> n ≤ m := by
  simp only [shiftRight_eq_div_pow]
  apply Nat.div_le_self

/-!
### testBit
We define an operation for testing individual bits in the binary representation
of a number.
-/

/--
Returns `true` if the `(n+1)`th least significant bit is `1`, or `false` if it is `0`.
-/
@[expose] def testBit (m n : Nat) : Bool :=
  -- `1 &&& n` is faster than `n &&& 1` for big `n`.
  1 &&& (m >>> n) != 0

end Nat
