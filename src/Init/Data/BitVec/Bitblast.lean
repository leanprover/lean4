/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan, Abdalrhman M Mohamed, Joe Hendrix
-/
prelude
import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod

/-!
# Bitblasting of bitvectors

This module provides theorems for showing the equivalence between BitVec operations using
the `Fin 2^n` representation and Boolean vectors.  It is still under development, but
intended to provide a path for converting SAT and SMT solver proofs about BitVectors
as vectors of bits into proofs about Lean `BitVec` values.

The module is named for the bit-blasting operation in an SMT solver that converts bitvector
expressions into expressions about individual bits in each vector.

## Main results
* `x + y : BitVec w` is `(adc x y false).2`.


## Future work
All other operations are to be PR'ed later and are already proved in
https://github.com/mhk119/lean-smt/blob/bitvec/Smt/Data/Bitwise.lean.

-/

open Nat Bool

namespace Bool

/-- At least two out of three booleans are true. -/
abbrev atLeastTwo (a b c : Bool) : Bool := a && b || a && c || b && c

@[simp] theorem atLeastTwo_false_left  : atLeastTwo false b c = (b && c) := by simp [atLeastTwo]
@[simp] theorem atLeastTwo_false_mid   : atLeastTwo a false c = (a && c) := by simp [atLeastTwo]
@[simp] theorem atLeastTwo_false_right : atLeastTwo a b false = (a && b) := by simp [atLeastTwo]
@[simp] theorem atLeastTwo_true_left   : atLeastTwo true b c  = (b || c) := by cases b <;> cases c <;> simp [atLeastTwo]
@[simp] theorem atLeastTwo_true_mid    : atLeastTwo a true c  = (a || c) := by cases a <;> cases c <;> simp [atLeastTwo]
@[simp] theorem atLeastTwo_true_right  : atLeastTwo a b true  = (a || b) := by cases a <;> cases b <;> simp [atLeastTwo]

end Bool

/-! ### Preliminaries -/

namespace BitVec

private theorem testBit_limit {x i : Nat} (x_lt_succ : x < 2^(i+1)) :
    testBit x i = decide (x ≥ 2^i) := by
  cases xi : testBit x i with
  | true =>
    simp [testBit_implies_ge xi]
  | false =>
    simp
    cases Nat.lt_or_ge x (2^i) with
    | inl x_lt =>
      exact x_lt
    | inr x_ge =>
      have ⟨j, ⟨j_ge, jp⟩⟩  := ge_two_pow_implies_high_bit_true x_ge
      cases Nat.lt_or_eq_of_le j_ge with
      | inr x_eq =>
        simp [x_eq, jp] at xi
      | inl x_lt =>
        exfalso
        apply Nat.lt_irrefl
        calc x < 2^(i+1) := x_lt_succ
             _ ≤ 2 ^ j := Nat.pow_le_pow_of_le_right Nat.zero_lt_two x_lt
             _ ≤ x := testBit_implies_ge jp

private theorem mod_two_pow_succ (x i : Nat) :
    x % 2^(i+1) = 2^i*(x.testBit i).toNat + x % (2 ^ i):= by
  rw [Nat.mod_pow_succ, Nat.add_comm, Nat.toNat_testBit]

private theorem mod_two_pow_add_mod_two_pow_add_bool_lt_two_pow_succ
     (x y i : Nat) (c : Bool) : x % 2^i + (y % 2^i + c.toNat) < 2^(i+1) := by
  have : c.toNat ≤ 1 := Bool.toNat_le c
  rw [Nat.pow_succ]
  omega

/-! ### Addition -/

/-- carry i x y c returns true if the `i` carry bit is true when computing `x + y + c`. -/
def carry (i : Nat) (x y : BitVec w) (c : Bool) : Bool :=
  decide (x.toNat % 2^i + y.toNat % 2^i + c.toNat ≥ 2^i)

@[simp] theorem carry_zero : carry 0 x y c = c := by
  cases c <;> simp [carry, mod_one]

theorem carry_succ (i : Nat) (x y : BitVec w) (c : Bool) :
    carry (i+1) x y c = atLeastTwo (x.getLsb i) (y.getLsb i) (carry i x y c) := by
  simp only [carry, mod_two_pow_succ, atLeastTwo, getLsb]
  simp only [Nat.pow_succ']
  have sum_bnd : x.toNat%2^i + (y.toNat%2^i + c.toNat) < 2*2^i := by
    simp only [← Nat.pow_succ']
    exact mod_two_pow_add_mod_two_pow_add_bool_lt_two_pow_succ ..
  cases x.toNat.testBit i <;> cases y.toNat.testBit i <;> (simp; omega)

/--
Does the addition of two `BitVec`s overflow?

The nice feature of this definition is that
it can be unfolded recursively to a circuit:
```
example (x y : BitVec 4) :
    addOverflow x y =
      atLeastTwo (x.getLsb 3) (y.getLsb 3) (atLeastTwo (x.getLsb 2) (y.getLsb 2)
        (atLeastTwo (x.getLsb 1) (y.getLsb 1) (x.getLsb 0 && y.getLsb 0))) := by
  simp [addOverflow, msb_truncate, BitVec.msb, getMsb]
```
-/
def addOverflow (x y : BitVec w) (c : Bool := false) : Bool :=
  match w with
  | 0 => c
  | (w + 1) => atLeastTwo x.msb y.msb (addOverflow (x.truncate w) (y.truncate w) c)

@[simp] theorem addOverflow_length_zero {x y : BitVec 0} : addOverflow x y c = c := rfl

theorem addOverflow_length_succ {x y : BitVec (w+1)} :
    addOverflow x y c = atLeastTwo x.msb y.msb (addOverflow (x.truncate w) (y.truncate w) c) :=
  rfl

@[simp] theorem addOverflow_zero_left_succ :
    addOverflow 0#(w+1) y c = (y.msb && addOverflow 0#w (y.truncate w) c) := by
  simp [addOverflow]

@[simp] theorem addOverflow_zero_right_succ {x : BitVec (w+1)} :
    addOverflow x 0#(w+1) c = (x.msb && addOverflow (x.truncate w) 0#w c) := by
  simp [addOverflow]

@[simp] theorem addOverflow_zero_zero :
    addOverflow 0#i 0#i c = (decide (i = 0) && c) := by
  cases i <;> simp

theorem carry_eq_addOverflow (i) (x y : BitVec w) (c) :
    carry i x y c = addOverflow (x.truncate i) (y.truncate i) c := by
  match i with
  | 0 => simp
  | (i + 1) =>
    rw [addOverflow_length_succ, carry_succ, carry_eq_addOverflow]
    simp [msb_zeroExtend, Nat.le_succ]

theorem addOverflow_eq_carry {x y : BitVec w} :
    addOverflow x y c = carry w x y c := by
  have := carry_eq_addOverflow w x y c
  simpa using this.symm

theorem addOverflow_cons_cons :
    addOverflow (cons a x) (cons b y) = atLeastTwo a b (addOverflow x y) := by
  simp [addOverflow]

theorem add_cons_cons (w) (x y : BitVec w) :
    (cons a x) + (cons b y) = cons (Bool.xor a (Bool.xor b (addOverflow x y))) (x + y) := by
  have pos : 0 < 2^w := Nat.pow_pos Nat.zero_lt_two
  apply eq_of_toNat_eq
  simp only [toNat_add, toNat_cons']
  rw [addOverflow_eq_carry, carry]
  simp [Nat.mod_pow_succ]
  by_cases h : 2 ^ w ≤ x.toNat + y.toNat
  · simp [h]
    have p : (x.toNat + y.toNat) / 2 ^ w = 1 := by
      apply Nat.div_eq_of_lt_le <;> omega
    cases a <;> cases b
      <;> simp [Nat.one_shiftLeft, Nat.add_left_comm x.toNat, Nat.add_assoc, p, pos]
      <;> simp [Nat.add_comm]
  · simp [h]
    have p : (x.toNat + y.toNat) / 2 ^ w = 0 := by
      apply Nat.div_eq_of_lt_le <;> omega
    cases a <;> cases b
      <;> simp [Nat.one_shiftLeft, Nat.add_left_comm x.toNat, Nat.add_assoc, p, pos]
      <;> simp [Nat.add_comm]

theorem msb_add (x y : BitVec w) :
    (x + y).msb =
      Bool.xor x.msb (Bool.xor y.msb (addOverflow (x.truncate (w-1)) (y.truncate (w-1)))) := by
  cases w with
  | zero => simp
  | succ w =>
    conv =>
      lhs
      rw [eq_msb_cons_truncate x, eq_msb_cons_truncate y, add_cons_cons]
    simp [succ_eq_add_one, Nat.add_one_sub_one]

/--
Variant of `getLsb_add` in terms of `addOverflow` rather than `carry`.
-/
theorem getLsb_add' (i : Nat) (x y : BitVec w) :
    getLsb (x + y) i = (decide (i < w) && Bool.xor (x.getLsb i)
      (Bool.xor (y.getLsb i) (addOverflow (x.truncate i) (y.truncate i)))) := by
  by_cases h : i < w
  · rw [← msb_truncate (x + y), truncate_add, msb_add, msb_truncate, msb_truncate]
    rw [Nat.add_one_sub_one, truncate_truncate_of_le, truncate_truncate_of_le]
    simp [h]
    all_goals omega
  · simp [h]
    simp at h
    simp [h]

theorem addOverflow_eq_false_of_and_eq_zero {x y : BitVec w} (h : x &&& y = 0#w) :
    addOverflow x y = false := by
  induction w with
  | zero => rfl
  | succ w ih =>
    have h₁ := congrArg BitVec.msb h
    have h₂ := congrArg (·.truncate w) h
    simp at h₁ h₂
    simp_all [addOverflow_length_succ]

theorem or_eq_add_of_and_eq_zero (x y : BitVec w) (h : x &&& y = 0) :
    x ||| y = x + y := by
  ext i
  have h₁ := congrArg (getLsb · i) h
  have h₂ := congrArg (truncate i) h
  simp at h₁ h₂
  simp only [getLsb_add', getLsb_or]
  rw [addOverflow_eq_false_of_and_eq_zero h₂]
  -- sat
  revert h₁
  cases x.getLsb i <;> cases y.getLsb i <;> simp

/-- Carry function for bitwise addition. -/
def adcb (x y c : Bool) : Bool × Bool := (atLeastTwo x y c, Bool.xor x (Bool.xor y c))

/-- Bitwise addition implemented via a ripple carry adder. -/
def adc (x y : BitVec w) : Bool → Bool × BitVec w :=
  iunfoldr fun (i : Fin w) c => adcb (x.getLsb i) (y.getLsb i) c

theorem getLsb_add_add_bool {i : Nat} (i_lt : i < w) (x y : BitVec w) (c : Bool) :
    getLsb (x + y + zeroExtend w (ofBool c)) i =
      Bool.xor (getLsb x i) (Bool.xor (getLsb y i) (carry i x y c)) := by
  let ⟨x, x_lt⟩ := x
  let ⟨y, y_lt⟩ := y
  simp only [getLsb, toNat_add, toNat_zeroExtend, i_lt, toNat_ofFin, toNat_ofBool,
    Nat.mod_add_mod, Nat.add_mod_mod]
  apply Eq.trans
  rw [← Nat.div_add_mod x (2^i), ← Nat.div_add_mod y (2^i)]
  simp only
    [ Nat.testBit_mod_two_pow,
      Nat.testBit_mul_two_pow_add_eq,
      i_lt,
      decide_True,
      Bool.true_and,
      Nat.add_assoc,
      Nat.add_left_comm (_%_) (_ * _) _,
      testBit_limit (mod_two_pow_add_mod_two_pow_add_bool_lt_two_pow_succ x y i c)
    ]
  simp [testBit_to_div_mod, carry, Nat.add_assoc]

theorem getLsb_add {i : Nat} (i_lt : i < w) (x y : BitVec w) :
    getLsb (x + y) i =
      Bool.xor (getLsb x i) (Bool.xor (getLsb y i) (carry i x y false)) := by
  simpa using getLsb_add_add_bool i_lt x y false

theorem adc_spec (x y : BitVec w) (c : Bool) :
    adc x y c = (carry w x y c, x + y + zeroExtend w (ofBool c)) := by
  simp only [adc]
  apply iunfoldr_replace
          (fun i => carry i x y c)
          (x + y + zeroExtend w (ofBool c))
          c
  case init =>
    simp [carry, Nat.mod_one]
    cases c <;> rfl
  case step =>
    simp [adcb, Prod.mk.injEq, carry_succ, getLsb_add_add_bool]

theorem add_eq_adc (w : Nat) (x y : BitVec w) : x + y = (adc x y false).snd := by
  simp [adc_spec]

/-! ### add -/

/-- Adding a bitvector to its own complement yields the all ones bitpattern -/
@[simp] theorem add_not_self (x : BitVec w) : x + ~~~x = allOnes w := by
  rw [add_eq_adc, adc, iunfoldr_replace (fun _ => false) (allOnes w)]
  · rfl
  · simp [adcb, atLeastTwo]

/-- Subtracting `x` from the all ones bitvector is equivalent to taking its complement -/
theorem allOnes_sub_eq_not (x : BitVec w) : allOnes w - x = ~~~x := by
  rw [← add_not_self x, BitVec.add_comm, add_sub_cancel]

end BitVec
