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

/-- Addition of bitvectors is the same as bitwise or, if bitwise and is zero. -/
theorem add_eq_or_of_and_eq_zero {w : Nat} (x y : BitVec w)
    (h : x &&& y = 0#w) : x + y = x ||| y := by
  rw [add_eq_adc, adc, iunfoldr_replace (fun _ => false) (x ||| y)]
  · rfl
  · simp only [adcb, atLeastTwo, Bool.and_false, Bool.or_false, bne_false, getLsb_or,
    Prod.mk.injEq, and_eq_false_imp]
    intros i
    replace h : (x &&& y).getLsb i = (0#w).getLsb i := by rw [h]
    simp only [getLsb_and, getLsb_zero, and_eq_false_imp] at h
    constructor
    · intros hx
      simp_all [hx]
    · by_cases hx : x.getLsb i <;> simp_all [hx]

/-! ### Negation -/

theorem bit_not_testBit (x : BitVec w) (i : Fin w) :
  getLsb (((iunfoldr (fun (i : Fin w) c => (c, !(x.getLsb i)))) ()).snd) i.val = !(getLsb x i.val) := by
  apply iunfoldr_getLsb (fun _ => ()) i (by simp)

theorem bit_not_add_self (x : BitVec w) :
  ((iunfoldr (fun (i : Fin w) c => (c, !(x.getLsb i)))) ()).snd + x  = -1 := by
  simp only [add_eq_adc]
  apply iunfoldr_replace_snd (fun _ => false) (-1) false rfl
  intro i; simp only [ BitVec.not, adcb, testBit_toNat]
  rw [iunfoldr_replace_snd (fun _ => ()) (((iunfoldr (fun i c => (c, !(x.getLsb i)))) ()).snd)]
  <;> simp [bit_not_testBit, negOne_eq_allOnes, getLsb_allOnes]

theorem bit_not_eq_not (x : BitVec w) :
  ((iunfoldr (fun i c => (c, !(x.getLsb i)))) ()).snd = ~~~ x := by
  simp [←allOnes_sub_eq_not, BitVec.eq_sub_iff_add_eq.mpr (bit_not_add_self x), ←negOne_eq_allOnes]

theorem bit_neg_eq_neg (x : BitVec w) : -x = (adc (((iunfoldr (fun (i : Fin w) c => (c, !(x.getLsb i)))) ()).snd) (BitVec.ofNat w 1) false).snd:= by
  simp only [← add_eq_adc]
  rw [iunfoldr_replace_snd ((fun _ => ())) (((iunfoldr (fun (i : Fin w) c => (c, !(x.getLsb i)))) ()).snd) _ rfl]
  · rw [BitVec.eq_sub_iff_add_eq.mpr (bit_not_add_self x), sub_toAdd, BitVec.add_comm _ (-x)]
    simp [← sub_toAdd, BitVec.sub_add_cancel]
  · simp [bit_not_testBit x _]

/-! ### Inequalities (le / lt) -/

theorem ult_eq_not_carry (x y : BitVec w) : x.ult y = !carry w x (~~~y) true := by
  simp only [BitVec.ult, carry, toNat_mod_cancel, toNat_not, toNat_true, ge_iff_le, ← decide_not,
    Nat.not_le, decide_eq_decide]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem ule_eq_not_ult (x y : BitVec w) : x.ule y = !y.ult x := by
  simp [BitVec.ule, BitVec.ult, ← decide_not]

theorem ule_eq_carry (x y : BitVec w) : x.ule y = carry w y (~~~x) true := by
  simp [ule_eq_not_ult, ult_eq_not_carry]

/-- If two bitvectors have the same `msb`, then signed and unsigned comparisons coincide -/
theorem slt_eq_ult_of_msb_eq {x y : BitVec w} (h : x.msb = y.msb) :
    x.slt y = x.ult y := by
  simp only [BitVec.slt, toInt_eq_msb_cond, BitVec.ult, decide_eq_decide, h]
  cases y.msb <;> simp

/-- If two bitvectors have different `msb`s, then unsigned comparison is determined by this bit -/
theorem ult_eq_msb_of_msb_neq {x y : BitVec w} (h : x.msb ≠ y.msb) :
    x.ult y = y.msb := by
  simp only [BitVec.ult, msb_eq_decide, ne_eq, decide_eq_decide] at *
  omega

/-- If two bitvectors have different `msb`s, then signed and unsigned comparisons are opposites -/
theorem slt_eq_not_ult_of_msb_neq {x y : BitVec w} (h : x.msb ≠ y.msb) :
    x.slt y = !x.ult y := by
  simp only [BitVec.slt, toInt_eq_msb_cond, Bool.eq_not_of_ne h, ult_eq_msb_of_msb_neq h]
  cases y.msb <;> (simp; omega)

theorem slt_eq_ult (x y : BitVec w) :
    x.slt y = (x.msb != y.msb).xor (x.ult y) := by
  by_cases h : x.msb = y.msb
  · simp [h, slt_eq_ult_of_msb_eq]
  · have h' : x.msb != y.msb := by simp_all
    simp [slt_eq_not_ult_of_msb_neq h, h']

theorem slt_eq_not_carry (x y : BitVec w) :
    x.slt y = (x.msb == y.msb).xor (carry w x (~~~y) true) := by
  simp only [slt_eq_ult, bne, ult_eq_not_carry]
  cases x.msb == y.msb <;> simp

theorem sle_eq_not_slt (x y : BitVec w) : x.sle y = !y.slt x := by
  simp only [BitVec.sle, BitVec.slt, ← decide_not, decide_eq_decide]; omega

theorem sle_eq_carry (x y : BitVec w) :
    x.sle y = !((x.msb == y.msb).xor (carry w y (~~~x) true)) := by
  rw [sle_eq_not_slt, slt_eq_not_carry, beq_comm]

/-! ### mul recurrence for bitblasting -/

/--
A recurrence that describes multiplication as repeated addition.
Is useful for bitblasting multiplication.
-/
def mulRec (l r : BitVec w) (s : Nat) : BitVec w :=
  let cur := if r.getLsb s then (l <<< s) else 0
  match s with
  | 0 => cur
  | s + 1 => mulRec l r s + cur

theorem mulRec_zero_eq (l r : BitVec w) :
    mulRec l r 0 = if r.getLsb 0 then l else 0 := by
  simp [mulRec]

theorem mulRec_succ_eq (l r : BitVec w) (s : Nat) :
    mulRec l r (s + 1) = mulRec l r s + if r.getLsb (s + 1) then (l <<< (s + 1)) else 0 := rfl

/--
When the `(i+1)`th bit of `x` is false,
keeping the lower `(i + 1)` bits of `x` equals keeping the lower `i` bits.
-/
theorem zeroExtend_truncate_succ_eq_zeroExtend_truncate_of_getLsb_false
  {x : BitVec w} {i : Nat} (hx : x.getLsb i = false) :
    zeroExtend w (x.truncate (i + 1)) =
      zeroExtend w (x.truncate i) := by
  ext k
  simp only [getLsb_zeroExtend, Fin.is_lt, decide_True, Bool.true_and, getLsb_or, getLsb_and]
  by_cases hik : i = k
  · subst hik
    simp [hx]
  · by_cases hik' : k < i + 1 <;> simp [hik'] <;> omega

/--
When the `(i+1)`th bit of `x` is true,
keeping the lower `(i + 1)` bits of `x` equalsk eeping the lower `i` bits
and then performing bitwise-or with `twoPow i = (1 << i)`,
-/
theorem zeroExtend_truncate_succ_eq_zeroExtend_truncate_or_twoPow_of_getLsb_true
    {x : BitVec w} {i : Nat} (hx : x.getLsb i = true) :
    zeroExtend w (x.truncate (i + 1)) =
      zeroExtend w (x.truncate i) ||| (twoPow w i) := by
  ext k
  simp only [getLsb_zeroExtend, Fin.is_lt, decide_True, Bool.true_and, getLsb_or, getLsb_and]
  by_cases hik : i = k
  · subst hik
    simp [hx]
  · by_cases hik' : k < i + 1 <;> simp [hik, hik'] <;> omega

/--
Recurrence lemma: truncating to `i+1` bits and then zero extending to `w`
equals truncating upto `i` bits `[0..i-1]`, and then adding the `i`th bit of `x`.
-/
theorem zeroExtend_truncate_succ_eq_zeroExtend_truncate_add_twoPow (x : BitVec w) (i : Nat) :
    zeroExtend w (x.truncate (i + 1)) =
      zeroExtend w (x.truncate i) + (x &&& twoPow w i) := by
  rw [add_eq_or_of_and_eq_zero]
  · ext k
    simp only [getLsb_zeroExtend, Fin.is_lt, decide_True, Bool.true_and, getLsb_or, getLsb_and]
    by_cases hik : i = k
    · subst hik
      simp
    · simp only [getLsb_twoPow, hik, decide_False, Bool.and_false, Bool.or_false]
      by_cases hik' : k < (i + 1)
      · have hik'' : k < i := by omega
        simp [hik', hik'']
      · have hik'' : ¬ (k < i) := by omega
        simp [hik', hik'']
  · ext k
    simp
    omega

/--
Recurrence lemma: multiplying `l` with the first `s` bits of `r` is the
same as truncating `r` to `s` bits, then zero extending to the original length,
and performing the multplication. -/
theorem mulRec_eq_mul_signExtend_truncate (l r : BitVec w) (s : Nat) :
    mulRec l r s = l * ((r.truncate (s + 1)).zeroExtend w) := by
  induction s
  case zero =>
    simp only [mulRec_zero_eq, ofNat_eq_ofNat, Nat.reduceAdd]
    by_cases r.getLsb 0
    case pos hr =>
      simp only [hr, ↓reduceIte, truncate, zeroExtend_one_eq_ofBool_getLsb_zero,
        hr, ofBool_true, ofNat_eq_ofNat]
      rw [zeroExtend_ofNat_one_eq_ofNat_one_of_lt (by omega)]
      simp
    case neg hr =>
      simp [hr, zeroExtend_one_eq_ofBool_getLsb_zero]
  case succ s' hs =>
    rw [mulRec_succ_eq, hs]
    have heq :
      (if r.getLsb (s' + 1) = true then l <<< (s' + 1) else 0) =
        (l * (r &&& (BitVec.twoPow w (s' + 1)))) := by
      simp only [ofNat_eq_ofNat, and_twoPow_eq]
      by_cases hr : r.getLsb (s' + 1) <;> simp [hr]
    rw [heq, ← BitVec.mul_add, ← zeroExtend_truncate_succ_eq_zeroExtend_truncate_add_twoPow]

theorem getLsb_mul (x y : BitVec w) (i : Nat) :
    (x * y).getLsb i = (mulRec x y w).getLsb i := by
  simp only [mulRec_eq_mul_signExtend_truncate]
  rw [truncate, ← truncate_eq_zeroExtend, ← truncate_eq_zeroExtend,
    truncate_truncate_of_le]
  · simp
  · omega

end BitVec
