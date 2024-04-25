/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Nat.Basic
import Init.Data.Nat.Div
import Init.Coe

/-- convert a `Bool` to a `Nat`, `false => 0`, `true => 1` -/
def Bool.toNat (b : Bool) : Nat := cond b 1 0

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

/-- `bit b` appends the digit `b` to the little end of the binary representation of
  its natural number input. -/
def bit (b : Bool) (n : Nat) : Nat :=
  cond b (n + n + 1) (n + n)

/-!
### testBit
We define an operation for testing individual bits in the binary representation
of a number.
-/

/-- `testBit m n` returns whether the `(n+1)` least significant bit is `1` or `0`-/
def testBit (m n : Nat) : Bool := 1 &&& (m >>> n) != 0
-- `1 &&& n` is faster than `n &&& 1` for big `n`. This may change in the future.

theorem bit_val (b n) : bit b n = 2 * n + b.toNat := by
  rw [Nat.mul_comm]
  induction b with
  | false => exact congrArg (· + n) n.zero_add.symm
  | true => exact congrArg (· + n + 1) n.zero_add.symm

theorem shiftRight_one (n) : n >>> 1 = n / 2 := rfl

theorem mod_two_eq_zero_or_one (n : Nat) : n % 2 = 0 ∨ n % 2 = 1 :=
  match n % 2, @Nat.mod_lt n 2 (by decide) with
  | 0, _ => .inl rfl
  | 1, _ => .inr rfl

@[simp] theorem one_land_eq_mod_two (n : Nat) : 1 &&& n = n % 2 := by
  match Nat.decEq n 0 with
  | isTrue n0 => subst n0; decide
  | isFalse n0 =>
    simp only [HAnd.hAnd, AndOp.and, land]
    unfold bitwise
    cases mod_two_eq_zero_or_one n with | _ h => simp [n0, h]; rfl

@[simp]
theorem testBit_zero (n : Nat) : testBit n 0 = decide (n % 2 = 1) := by
  cases mod_two_eq_zero_or_one n with | _ h => simp [testBit, h]

@[simp] theorem decide_mod_two_eq_one_toNat (n : Nat) : (decide (n % 2 = 1)).toNat = n % 2 := by
  cases mod_two_eq_zero_or_one n with | _ h => simp [h]; rfl

theorem testBit_zero_toNat (n : Nat) : (n.testBit 0).toNat = n % 2 := by simp

theorem bit_decomp (n : Nat) : bit (n.testBit 0) (n >>> 1) = n := by
  simp [bit_val, shiftRight_one, Nat.div_add_mod]

theorem bit_eq_zero_iff {n : Nat} {b : Bool} : bit b n = 0 ↔ n = 0 ∧ b = false := by
  cases n <;> cases b <;> simp [bit, ← Nat.add_assoc]

/-- For a predicate `C : Nat → Sort u`, if instances can be
  constructed for natural numbers of the form `bit b n`,
  they can be constructed for any given natural number. -/
@[inline]
def bitCasesOn {C : Nat → Sort u} (n) (h : ∀ b n, C (bit b n)) : C n := bit_decomp n ▸ h _ _

/-- A recursion principle for `bit` representations of natural numbers.
  For a predicate `C : Nat → Sort u`, if instances can be
  constructed for natural numbers of the form `bit b n`,
  they can be constructed for all natural numbers. -/
@[elab_as_elim, specialize]
def binaryRec {C : Nat → Sort u} (z : C 0) (f : ∀ b n, C n → C (bit b n)) (n : Nat) : C n :=
  if n0 : n = 0 then congrArg C n0 ▸ z -- `congrArg C _` is `rfl` in non-dependent case
  else congrArg C n.bit_decomp ▸ f (1 &&& n != 0) (n >>> 1) (binaryRec z f (n >>> 1))
decreasing_by exact bitwise_rec_lemma n0

/-- The same as `binaryRec`, but the induction step can assume that if `n=0`,
  the bit being appended is `true`-/
@[elab_as_elim, specialize]
def binaryRec' {C : Nat → Sort u} (z : C 0)
    (f : ∀ b n, (n = 0 → b = true) → C n → C (bit b n)) : ∀ n, C n :=
  binaryRec z fun b n ih =>
    if h : n = 0 → b = true then f b n h ih
    else
      have : bit b n = 0 := by
        rw [bit_eq_zero_iff]
        cases n <;> cases b <;> simp at h <;> simp [h]
      congrArg C this ▸ z

/-- The same as `binaryRec`, but special casing both 0 and 1 as base cases -/
@[elab_as_elim, specialize]
def binaryRecFromOne {C : Nat → Sort u} (z₀ : C 0) (z₁ : C 1)
    (f : ∀ b n, n ≠ 0 → C n → C (bit b n)) : ∀ n, C n :=
  binaryRec' z₀ fun b n h ih =>
    if h' : n = 0 then by
      rw [h', h h']
      exact z₁
    else f b n h' ih

end Nat
