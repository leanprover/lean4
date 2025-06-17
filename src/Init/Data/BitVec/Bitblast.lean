/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan, Abdalrhman M Mohamed, Joe Hendrix, Siddharth Bhat
-/
module

prelude
import all Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Mod
import all Init.Data.Int.DivMod
import Init.Data.Int.LemmasAux
import all Init.Data.BitVec.Basic
import Init.Data.BitVec.Decidable
import Init.Data.BitVec.Lemmas
import Init.Data.BitVec.Folds

/-!
# Bit blasting of bitvectors

This module provides theorems for showing the equivalence between BitVec operations using
the `Fin 2^n` representation and Boolean vectors.  It is still under development, but
intended to provide a path for converting SAT and SMT solver proofs about BitVectors
as vectors of bits into proofs about Lean `BitVec` values.

The module is named for the bit-blasting operation in an SMT solver that converts bitvector
expressions into expressions about individual bits in each vector.

### Example: How bit blasting works for multiplication

We explain how the lemmas here are used for bit blasting,
by using multiplication as a prototypical example.
Other bit blasters for other operations follow the same pattern.
To bit blast a multiplication of the form `x * y`,
we must unfold the above into a form that the SAT solver understands.

We assume that the solver already knows how to bit blast addition.
This is known to `bv_decide`, by exploiting the lemma `add_eq_adc`,
which says that `x + y : BitVec w` equals `(adc x y false).2`,
where `adc` builds an add-carry circuit in terms of the primitive operations
(bitwise and, bitwise or, bitwise xor) that bv_decide already understands.
In this way, we layer bit blasters on top of each other,
by reducing the multiplication bit blaster to an addition operation.

The core lemma is given by `getLsbD_mul`:

```lean
 x y : BitVec w ⊢ (x * y).getLsbD i = (mulRec x y w).getLsbD i
```

Which says that the `i`th bit of `x * y` can be obtained by
evaluating the `i`th bit of `(mulRec x y w)`.
Once again, we assume that `bv_decide` knows how to implement `getLsbD`,
given that `mulRec` can be understood by `bv_decide`.

We write two lemmas to enable `bv_decide` to unfold `(mulRec x y w)`
into a complete circuit, **when `w` is a known constant**`.
This is given by two recurrence lemmas, `mulRec_zero_eq` and `mulRec_succ_eq`,
which are applied repeatedly when the width is `0` and when the width is `w' + 1`:

```lean
mulRec_zero_eq :
    mulRec x y 0 =
      if y.getLsbD 0 then x else 0

mulRec_succ_eq
    mulRec x y (s + 1) =
      mulRec x y s +
      if y.getLsbD (s + 1) then (x <<< (s + 1)) else 0 := rfl
```

By repeatedly applying the lemmas `mulRec_zero_eq` and `mulRec_succ_eq`,
one obtains a circuit for multiplication.
Note that this circuit uses `BitVec.add`, `BitVec.getLsbD`, `BitVec.shiftLeft`.
Here, `BitVec.add` and `BitVec.shiftLeft` are (recursively) bit blasted by `bv_decide`,
using the lemmas `add_eq_adc` and `shiftLeft_eq_shiftLeftRec`,
and `BitVec.getLsbD` is a primitive that `bv_decide` knows how to reduce to SAT.

The two lemmas, `mulRec_zero_eq`, and `mulRec_succ_eq`,
are used in `Std.Tactic.BVDecide.BVExpr.bitblast.blastMul`
to prove the correctness of the circuit that is built by `bv_decide`.

```lean
def blastMul (aig : AIG BVBit) (input : AIG.BinaryRefVec aig w) : AIG.RefVecEntry BVBit w
theorem denote_blastMul (aig : AIG BVBit) (lhs rhs : BitVec w) (assign : Assignment) :
   ...
   ⟦(blastMul aig input).aig, (blastMul aig input).vec[idx], assign.toAIGAssignment⟧
     =
   (lhs * rhs).getLsbD idx
```

The definition and theorem above are internal to `bv_decide`,
and use `mulRec_{zero,succ}_eq` to prove that the circuit built by `bv_decide`
computes the correct value for multiplication.

To zoom out, therefore, we follow two steps:
First, we prove bitvector lemmas to unfold a high-level operation (such as multiplication)
into already bit blastable operations (such as addition and left shift).
We then use these lemmas to prove the correctness of the circuit that `bv_decide` builds.

We use this workflow to implement bit blasting for all SMT-LIB v2 operations.

## Main results
* `x + y : BitVec w` is `(adc x y false).2`.


## Future work
All other operations are to be PR'ed later and are already proved in
https://github.com/mhk119/lean-smt/blob/bitvec/Smt/Data/Bitwise.lean.

-/

set_option linter.missingDocs true

open Nat Bool

namespace Bool

/--
At least two out of three Booleans are true.

This function is typically used to model addition of binary numbers, to combine a carry bit with two
addend bits.
-/
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
    simp [Nat.ge_two_pow_of_testBit xi]
  | false =>
    simp
    cases Nat.lt_or_ge x (2^i) with
    | inl x_lt =>
      exact x_lt
    | inr x_ge =>
      have ⟨j, ⟨j_ge, jp⟩⟩  := exists_ge_and_testBit_of_ge_two_pow x_ge
      cases Nat.lt_or_eq_of_le j_ge with
      | inr x_eq =>
        simp [x_eq, jp] at xi
      | inl x_lt =>
        exfalso
        apply Nat.lt_irrefl
        calc x < 2^(i+1) := x_lt_succ
             _ ≤ 2 ^ j := Nat.pow_le_pow_right Nat.zero_lt_two x_lt
             _ ≤ x := ge_two_pow_of_testBit jp

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
    carry (i+1) x y c = atLeastTwo (x.getLsbD i) (y.getLsbD i) (carry i x y c) := by
  simp only [carry, mod_two_pow_succ, atLeastTwo, getLsbD]
  simp only [Nat.pow_succ']
  have sum_bnd : x.toNat%2^i + (y.toNat%2^i + c.toNat) < 2*2^i := by
    simp only [← Nat.pow_succ']
    exact mod_two_pow_add_mod_two_pow_add_bool_lt_two_pow_succ ..
  cases x.toNat.testBit i <;> cases y.toNat.testBit i <;> (simp; omega)

theorem carry_succ_one (i : Nat) (x : BitVec w) (h : 0 < w) :
    carry (i+1) x (1#w) false = decide (∀ j ≤ i, x.getLsbD j = true) := by
  induction i with
  | zero => simp [carry_succ, h]
  | succ i ih =>
    rw [carry_succ, ih]
    simp only [getLsbD_one, add_one_ne_zero, decide_false, Bool.and_false, atLeastTwo_false_mid]
    cases hx : x.getLsbD (i+1)
    case false =>
      have : ∃ j ≤ i + 1, x.getLsbD j = false :=
        ⟨i+1, by omega, hx⟩
      simpa
    case true =>
      suffices
          (∀ (j : Nat), j ≤ i → x.getLsbD j = true)
          ↔ (∀ (j : Nat), j ≤ i + 1 → x.getLsbD j = true) by
        simpa
      constructor
      · intro h j hj
        rcases Nat.le_or_eq_of_le_succ hj with (hj' | rfl)
        · apply h; assumption
        · exact hx
      · intro h j hj; apply h; omega

/--
If `x &&& y = 0`, then the carry bit `(x + y + 0)` is always `false` for any index `i`.
Intuitively, this is because a carry is only produced when at least two of `x`, `y`, and the
previous carry are true. However, since `x &&& y = 0`, at most one of `x, y` can be true,
and thus we never have a previous carry, which means that the sum cannot produce a carry.
-/
theorem carry_of_and_eq_zero {x y : BitVec w} (h : x &&& y = 0#w) : carry i x y false = false := by
  induction i with
  | zero => simp
  | succ i ih =>
    replace h := congrArg (·.getLsbD i) h
    simp_all [carry_succ]

/-- The final carry bit when computing `x + y + c` is `true` iff `x.toNat + y.toNat + c.toNat ≥ 2^w`. -/
theorem carry_width {x y : BitVec w} :
    carry w x y c = decide (x.toNat + y.toNat + c.toNat ≥ 2^w) := by
  simp [carry]

/--
If `x &&& y = 0`, then addition does not overflow, and thus `(x + y).toNat = x.toNat + y.toNat`.
-/
theorem toNat_add_of_and_eq_zero {x y : BitVec w} (h : x &&& y = 0#w) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [toNat_add]
  apply Nat.mod_eq_of_lt
  suffices ¬ decide (x.toNat + y.toNat + false.toNat ≥ 2^w) by
    simp only [decide_eq_true_eq] at this
    omega
  rw [← carry_width]
  simp [not_eq_true, carry_of_and_eq_zero h]

/-- Carry function for bitwise addition. -/
def adcb (x y c : Bool) : Bool × Bool := (atLeastTwo x y c, x ^^ (y ^^ c))

/-- Bitwise addition implemented via a ripple carry adder. -/
def adc (x y : BitVec w) : Bool → Bool × BitVec w :=
  iunfoldr fun (i : Fin w) c => adcb (x.getLsbD i) (y.getLsbD i) c

theorem getLsbD_add_add_bool {i : Nat} (i_lt : i < w) (x y : BitVec w) (c : Bool) :
    getLsbD (x + y + setWidth w (ofBool c)) i =
      (getLsbD x i ^^ (getLsbD y i ^^ carry i x y c)) := by
  let ⟨x, x_lt⟩ := x
  let ⟨y, y_lt⟩ := y
  simp only [getLsbD, toNat_add, toNat_setWidth, i_lt, toNat_ofFin, toNat_ofBool,
    Nat.mod_add_mod, Nat.add_mod_mod]
  apply Eq.trans
  rw [← Nat.div_add_mod x (2^i), ← Nat.div_add_mod y (2^i)]
  simp only
    [ Nat.testBit_mod_two_pow,
      Nat.testBit_mul_two_pow_add_eq,
      i_lt,
      decide_true,
      Bool.true_and,
      Nat.add_assoc,
      Nat.add_left_comm (_%_) (_ * _) _,
      testBit_limit (mod_two_pow_add_mod_two_pow_add_bool_lt_two_pow_succ x y i c)
    ]
  simp [testBit_eq_decide_div_mod_eq, carry, Nat.add_assoc]

theorem getLsbD_add {i : Nat} (i_lt : i < w) (x y : BitVec w) :
    getLsbD (x + y) i =
      (getLsbD x i ^^ (getLsbD y i ^^ carry i x y false)) := by
  simpa using getLsbD_add_add_bool i_lt x y false

theorem getElem_add_add_bool {i : Nat} (i_lt : i < w) (x y : BitVec w) (c : Bool) :
    (x + y + setWidth w (ofBool c))[i] =
      (x[i] ^^ (y[i] ^^ carry i x y c)) := by
  simp only [← getLsbD_eq_getElem]
  rw [getLsbD_add_add_bool]
  omega

theorem getElem_add {i : Nat} (i_lt : i < w) (x y : BitVec w) :
    (x + y)[i] = (x[i] ^^ (y[i] ^^ carry i x y false)) := by
  simpa using getElem_add_add_bool i_lt x y false

theorem adc_spec (x y : BitVec w) (c : Bool) :
    adc x y c = (carry w x y c, x + y + setWidth w (ofBool c)) := by
  simp only [adc]
  apply iunfoldr_replace
          (fun i => carry i x y c)
          (x + y + setWidth w (ofBool c))
          c
  case init =>
    simp [carry, Nat.mod_one]
    cases c <;> rfl
  case step =>
    simp [adcb, Prod.mk.injEq, carry_succ, getElem_add_add_bool]

theorem add_eq_adc (w : Nat) (x y : BitVec w) : x + y = (adc x y false).snd := by
  simp [adc_spec]

/-! ### add -/

theorem getMsbD_add {i : Nat} {i_lt : i < w} {x y : BitVec w} :
    getMsbD (x + y) i =
      Bool.xor (getMsbD x i) (Bool.xor (getMsbD y i) (carry (w - 1 - i) x y false)) := by
  simp [getMsbD, getElem_add, i_lt, show w - 1 - i < w by omega]

theorem msb_add {w : Nat} {x y: BitVec w} :
    (x + y).msb =
      Bool.xor x.msb (Bool.xor y.msb (carry (w - 1) x y false)) := by
  simp only [BitVec.msb, BitVec.getMsbD]
  by_cases h : w ≤ 0
  · simp [h, show w = 0 by omega]
  · rw [getLsbD_add (x := x)]
    simp [show w > 0 by omega]
    omega

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
  · simp only [adcb, atLeastTwo, Bool.and_false, Bool.or_false, bne_false, getLsbD_or,
    Prod.mk.injEq, and_eq_false_imp]
    intros i
    replace h : (x &&& y).getLsbD i = (0#w).getLsbD i := by rw [h]
    simp only [getLsbD_and, getLsbD_zero, and_eq_false_imp] at h
    constructor
    · intros hx
      simp_all [hx]
    · by_cases hx : x.getLsbD i <;> simp_all [hx]

/-! ### Sub-/

theorem getLsbD_sub {i : Nat} {i_lt : i < w} {x y : BitVec w} :
    (x - y).getLsbD i
      = (x.getLsbD i ^^ ((~~~y + 1#w).getLsbD i ^^ carry i x (~~~y + 1#w) false)) := by
  rw [sub_eq_add_neg, BitVec.neg_eq_not_add, getLsbD_add]
  omega

theorem getMsbD_sub {i : Nat} {i_lt : i < w} {x y : BitVec w} :
    (x - y).getMsbD i =
      (x.getMsbD i ^^ ((~~~y + 1).getMsbD i ^^ carry (w - 1 - i) x (~~~y + 1) false)) := by
  rw [sub_eq_add_neg, neg_eq_not_add, getMsbD_add]
  · rfl
  · omega

theorem getElem_sub {i : Nat} {x y : BitVec w} (h : i < w) :
    (x - y)[i] = (x[i] ^^ ((~~~y + 1#w)[i] ^^ carry i x (~~~y + 1#w) false)) := by
  simp [← getLsbD_eq_getElem, getLsbD_sub, h]

theorem msb_sub {x y: BitVec w} :
    (x - y).msb
      = (x.msb ^^ ((~~~y + 1#w).msb ^^ carry (w - 1 - 0) x (~~~y + 1#w) false)) := by
  simp [sub_eq_add_neg, BitVec.neg_eq_not_add, msb_add]

/-! ### Negation -/

theorem bit_not_testBit (x : BitVec w) (i : Fin w) :
  (((iunfoldr (fun (i : Fin w) c => (c, !(x[i.val])))) ()).snd)[i.val] = !(getLsbD x i.val) := by
  apply iunfoldr_getLsbD (fun _ => ()) i (by simp)

theorem bit_not_add_self (x : BitVec w) :
  ((iunfoldr (fun (i : Fin w) c => (c, !(x[i.val])))) ()).snd + x  = -1 := by
  simp only [add_eq_adc]
  apply iunfoldr_replace_snd (fun _ => false) (-1) false rfl
  intro i; simp only [adcb, Fin.is_lt, getLsbD_eq_getElem, atLeastTwo_false_right, bne_false,
    ofNat_eq_ofNat, Fin.getElem_fin, Prod.mk.injEq, and_eq_false_imp]
  rw [iunfoldr_replace_snd (fun _ => ()) (((iunfoldr (fun i c => (c, !(x[i.val])))) ()).snd)]
  <;> simp [bit_not_testBit, neg_one_eq_allOnes, getElem_allOnes]

theorem bit_not_eq_not (x : BitVec w) :
  ((iunfoldr (fun i c => (c, !(x[i])))) ()).snd = ~~~ x := by
  simp [←allOnes_sub_eq_not, BitVec.eq_sub_iff_add_eq.mpr (bit_not_add_self x), ←neg_one_eq_allOnes]

theorem bit_neg_eq_neg (x : BitVec w) : -x = (adc (((iunfoldr (fun (i : Fin w) c => (c, !(x[i.val])))) ()).snd) (BitVec.ofNat w 1) false).snd:= by
  simp only [← add_eq_adc]
  rw [iunfoldr_replace_snd ((fun _ => ())) (((iunfoldr (fun (i : Fin w) c => (c, !(x[i.val])))) ()).snd) _ rfl]
  · rw [BitVec.eq_sub_iff_add_eq.mpr (bit_not_add_self x), sub_eq_add_neg, BitVec.add_comm _ (-x)]
    simp [← sub_eq_add_neg, BitVec.sub_add_cancel]
  · simp [bit_not_testBit x _]

/--
Remember that negating a bitvector is equal to incrementing the complement
by one, i.e., `-x = ~~~x + 1`. See also `neg_eq_not_add`.

This computation has two crucial properties:
- The least significant bit of `-x` is the same as the least significant bit of `x`, and
- The `i+1`-th least significant bit of `-x` is the complement of the `i+1`-th bit of `x`, unless
  all of the preceding bits are `false`, in which case the bit is equal to the `i+1`-th bit of `x`
-/
theorem getLsbD_neg {i : Nat} {x : BitVec w} :
    getLsbD (-x) i =
      (getLsbD x i ^^ decide (i < w) && decide (∃ j < i, getLsbD x j = true)) := by
  rw [neg_eq_not_add]
  by_cases hi : i < w
  · rw [getLsbD_add hi]
    have : 0 < w := by omega
    simp only [getLsbD_not, hi, decide_true, Bool.true_and, getLsbD_one, this, not_bne,
      _root_.true_and, not_eq_eq_eq_not]
    cases i with
    | zero =>
      have carry_zero : carry 0 ?x ?y false = false := by
        simp [carry]; omega
      simp [hi, carry_zero]
    | succ =>
      rw [carry_succ_one _ _ (by omega), ← Bool.xor_not, ← decide_not]
      simp only [add_one_ne_zero, decide_false, getLsbD_not, and_eq_true, decide_eq_true_eq,
        not_eq_eq_eq_not, Bool.not_true, false_bne, not_exists, _root_.not_and, not_eq_true,
        bne_right_inj, decide_eq_decide]
      constructor
      · rintro h j hj; exact And.right <| h j (by omega)
      · rintro h j hj; exact ⟨by omega, h j (by omega)⟩
  · have h_ge : w ≤ i := by omega
    simp [getLsbD_of_ge _ _ h_ge, h_ge, hi]

theorem getElem_neg {i : Nat} {x : BitVec w} (h : i < w) :
    (-x)[i] = (x[i] ^^ decide (∃ j < i, x.getLsbD j = true)) := by
  simp [← getLsbD_eq_getElem, getLsbD_neg, h]

theorem getMsbD_neg {i : Nat} {x : BitVec w} :
    getMsbD (-x) i =
      (getMsbD x i ^^ decide (∃ j < w, i < j ∧ getMsbD x j = true)) := by
  simp only [getMsbD, getLsbD_neg, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq]
  by_cases hi : i < w
  case neg =>
    simp [hi]; omega
  case pos =>
    have h₁ : w - 1 - i < w := by omega
    simp only [hi, decide_true, h₁, Bool.true_and, Bool.bne_right_inj, decide_eq_decide]
    constructor
    · rintro ⟨j, hj, h⟩
      refine ⟨w - 1 - j, by omega, by omega, by omega, _root_.cast ?_ h⟩
      congr; omega
    · rintro ⟨j, hj₁, hj₂, -, h⟩
      exact ⟨w - 1 - j, by omega, h⟩

theorem msb_neg {w : Nat} {x : BitVec w} :
    (-x).msb = ((x != 0#w && x != intMin w) ^^ x.msb) := by
  simp only [BitVec.msb, getMsbD_neg]
  by_cases hmin : x = intMin _
  case pos =>
    have : (∃ j, j < w ∧ 0 < j ∧ 0 < w ∧ j = 0) ↔ False := by
      simp; omega
    simp [hmin, getMsbD_intMin, this]
  case neg =>
    by_cases hzero : x = 0#w
    case pos => simp [hzero]
    case neg =>
      have w_pos : 0 < w := by
        cases w
        · rw [@of_length_zero x] at hzero
          contradiction
        · omega
      suffices ∃ j, j < w ∧ 0 < j ∧ x.getMsbD j = true
        by simp [show x != 0#w by simpa, show x != intMin w by simpa, this]
      false_or_by_contra
      rename_i getMsbD_x
      simp only [not_exists, _root_.not_and, not_eq_true] at getMsbD_x
      /- `getMsbD` says that all bits except the msb are `false` -/
      cases hmsb : x.msb
      case true =>
        apply hmin
        apply eq_of_getMsbD_eq
        intro i hi
        simp only [getMsbD_intMin, w_pos, decide_true, Bool.true_and]
        cases i
        case zero => exact hmsb
        case succ => exact getMsbD_x _ hi (by omega)
      case false =>
        apply hzero
        apply eq_of_getMsbD_eq
        intro i hi
        simp only [getMsbD_zero]
        cases i
        case zero => exact hmsb
        case succ => exact getMsbD_x _ hi (by omega)

/-- This is false if `v < w` and `b = intMin`. See also `signExtend_neg_of_ne_intMin`. -/
@[simp] theorem signExtend_neg_of_le {v w : Nat} (h : w ≤ v) (b : BitVec v) :
    (-b).signExtend w = -b.signExtend w := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [getElem_signExtend, getElem_neg]
  rw [dif_pos (by omega), dif_pos (by omega)]
  simp only [getLsbD_signExtend, Bool.and_eq_true, decide_eq_true_eq, Bool.ite_eq_true_distrib,
    Bool.bne_right_inj, decide_eq_decide]
  exact ⟨fun ⟨j, hj₁, hj₂⟩ => ⟨j, ⟨hj₁, ⟨by omega, by rwa [if_pos (by omega)]⟩⟩⟩,
    fun ⟨j, hj₁, hj₂, hj₃⟩ => ⟨j, hj₁, by rwa [if_pos (by omega)] at hj₃⟩⟩

/-- This is false if `v < w` and `b = intMin`. See also `signExtend_neg_of_le`. -/
@[simp] theorem signExtend_neg_of_ne_intMin {v w : Nat} (b : BitVec v) (hb : b ≠ intMin v) :
    (-b).signExtend w = -b.signExtend w := by
  refine (by omega : w ≤ v ∨ v < w).elim (fun h => signExtend_neg_of_le h b) (fun h => ?_)
  apply BitVec.eq_of_toInt_eq
  rw [toInt_signExtend_of_le (by omega), toInt_neg_of_ne_intMin hb, toInt_neg_of_ne_intMin,
    toInt_signExtend_of_le (by omega)]
  apply ne_of_apply_ne BitVec.toInt
  rw [toInt_signExtend_of_le (by omega), toInt_intMin_of_pos (by omega)]
  have := b.le_two_mul_toInt
  have : -2 ^ w < -2 ^ v := by
    apply Int.neg_lt_neg
    norm_cast
    rwa [Nat.pow_lt_pow_iff_right (by omega)]
  have : 2 * b.toInt ≠ -2 ^ w := by omega
  rw [(show w = w - 1 + 1 by omega), Int.pow_succ] at this
  omega

/-! ### abs -/

theorem msb_abs {w : Nat} {x : BitVec w} :
    x.abs.msb = (decide (x = intMin w) && decide (0 < w)) := by
  simp only [BitVec.abs, getMsbD_neg, ne_eq, decide_not, Bool.not_bne]
  by_cases h₀ : 0 < w
  · by_cases h₁ : x = intMin w
    · simp [h₁, msb_intMin]
    · simp only [neg_eq, h₁, decide_false]
      by_cases h₂ : x.msb
      · simp [h₂, msb_neg]
        and_intros
        · by_cases h₃ : x = 0#w
          · simp [h₃] at h₂
          · simp [h₃]
        · simp [h₁]
      · simp [h₂]
  · simp [BitVec.msb, show w = 0 by omega]

/-! ### Inequalities (le / lt) -/

theorem ult_eq_not_carry (x y : BitVec w) : x.ult y = !carry w x (~~~y) true := by
  simp only [BitVec.ult, carry, toNat_mod_cancel, toNat_not, toNat_true, ge_iff_le, ← decide_not,
    Nat.not_le, decide_eq_decide]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem ule_eq_carry (x y : BitVec w) : x.ule y = carry w y (~~~x) true := by
  simp [ule_eq_not_ult, ult_eq_not_carry]

theorem slt_eq_not_carry {x y : BitVec w} :
    x.slt y = (x.msb == y.msb).xor (carry w x (~~~y) true) := by
  simp only [slt_eq_ult, bne, ult_eq_not_carry]
  cases x.msb == y.msb <;> simp

theorem sle_eq_carry {x y : BitVec w} :
    x.sle y = !((x.msb == y.msb).xor (carry w y (~~~x) true)) := by
  rw [sle_eq_not_slt, slt_eq_not_carry, beq_comm]

theorem neg_slt_zero (h : 0 < w) {x : BitVec w} :
    (-x).slt 0#w = ((x == intMin w) || (0#w).slt x) := by
  rw [slt_zero_eq_msb, msb_neg, slt_eq_sle_and_ne, zero_sle_eq_not_msb]
  apply Bool.eq_iff_iff.2
  cases hmsb : x.msb with
  | false => simpa [ne_intMin_of_msb_eq_false h hmsb] using Decidable.not_iff_not.2 (eq_comm)
  | true =>
    simp only [Bool.bne_true, Bool.not_and, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      bne_eq_false_iff_eq, Bool.false_and, Bool.or_false, beq_iff_eq,
      _root_.or_iff_right_iff_imp]
    rintro rfl
    simp at hmsb

theorem neg_sle_zero (h : 0 < w) {x : BitVec w} :
    (-x).sle 0#w = (x == intMin w || (0#w).sle x) := by
  rw [sle_eq_slt_or_eq, neg_slt_zero h, sle_eq_slt_or_eq]
  simp [Bool.beq_eq_decide_eq (-x), Bool.beq_eq_decide_eq _ x, Eq.comm (a := x), Bool.or_assoc]

/-! ### mul recurrence for bit blasting -/

/--
A recurrence that describes multiplication as repeated addition.

This function is useful for bit blasting multiplication.
-/
@[expose]
def mulRec (x y : BitVec w) (s : Nat) : BitVec w :=
  let cur := if y.getLsbD s then (x <<< s) else 0
  match s with
  | 0 => cur
  | s + 1 => mulRec x y s + cur

theorem mulRec_zero_eq (x y : BitVec w) :
    mulRec x y 0 = if y.getLsbD 0 then x else 0 := by
  simp [mulRec]

theorem mulRec_succ_eq (x y : BitVec w) (s : Nat) :
    mulRec x y (s + 1) = mulRec x y s + if y.getLsbD (s + 1) then (x <<< (s + 1)) else 0 := rfl

/--
Recurrence lemma: truncating to `i+1` bits and then zero extending to `w`
equals truncating upto `i` bits `[0..i-1]`, and then adding the `i`th bit of `x`.
-/
theorem setWidth_setWidth_succ_eq_setWidth_setWidth_add_twoPow (x : BitVec w) (i : Nat) :
    setWidth w (x.setWidth (i + 1)) =
      setWidth w (x.setWidth i) + (x &&& twoPow w i) := by
  rw [add_eq_or_of_and_eq_zero]
  · ext k h
    simp only [getElem_setWidth, getLsbD_setWidth, h, getLsbD_eq_getElem, getElem_or, getElem_and,
      getElem_twoPow]
    by_cases hik : i = k
    · subst hik
      simp [h]
    · by_cases hik' : k < (i + 1)
      · have hik'' : k < i := by omega
        simp [hik', hik'']
        omega
      · have hik'' : ¬ (k < i) := by omega
        simp [hik', hik'']
        omega
  · ext k
    simp only [and_twoPow, getLsbD_and, getLsbD_setWidth, Fin.is_lt, decide_true, Bool.true_and,
      getLsbD_zero, and_eq_false_imp, and_eq_true, decide_eq_true_eq, and_imp]
    by_cases hi : x.getLsbD i <;> simp [hi] <;> omega

/--
Recurrence lemma: multiplying `x` with the first `s` bits of `y` is the
same as truncating `y` to `s` bits, then zero extending to the original length,
and performing the multiplication. -/
theorem mulRec_eq_mul_signExtend_setWidth (x y : BitVec w) (s : Nat) :
    mulRec x y s = x * ((y.setWidth (s + 1)).setWidth w) := by
  induction s
  case zero =>
    simp only [mulRec_zero_eq, ofNat_eq_ofNat, Nat.reduceAdd]
    by_cases y.getLsbD 0
    case pos hy =>
      simp only [hy, ↓reduceIte, setWidth_one_eq_ofBool_getLsb_zero,
        ofBool_true, ofNat_eq_ofNat]
      rw [setWidth_ofNat_one_eq_ofNat_one_of_lt (by omega)]
      simp
    case neg hy =>
      simp [hy, setWidth_one_eq_ofBool_getLsb_zero]
  case succ s' hs =>
    rw [mulRec_succ_eq, hs]
    have heq :
      (if y.getLsbD (s' + 1) = true then x <<< (s' + 1) else 0) =
        (x * (y &&& (BitVec.twoPow w (s' + 1)))) := by
      simp only [ofNat_eq_ofNat, and_twoPow]
      by_cases hy : y.getLsbD (s' + 1) <;> simp [hy]
    rw [heq, ← BitVec.mul_add, ← setWidth_setWidth_succ_eq_setWidth_setWidth_add_twoPow]

theorem getLsbD_mul (x y : BitVec w) (i : Nat) :
    (x * y).getLsbD i = (mulRec x y w).getLsbD i := by
  simp only [mulRec_eq_mul_signExtend_setWidth]
  rw [setWidth_setWidth_of_le]
  · simp
  · omega

theorem mul_eq_mulRec {x y : BitVec w} :
    x * y = mulRec x y w := by
  apply eq_of_getLsbD_eq
  intro i hi
  apply getLsbD_mul

theorem getMsbD_mul (x y : BitVec w) (i : Nat) :
    (x * y).getMsbD i = (mulRec x y w).getMsbD i := by
  simp only [mulRec_eq_mul_signExtend_setWidth]
  rw [setWidth_setWidth_of_le]
  · simp
  · omega

theorem getElem_mul {x y : BitVec w} {i : Nat} (h : i < w) :
    (x * y)[i] = (mulRec x y w)[i] := by
  simp [mulRec_eq_mul_signExtend_setWidth]

/-! ## shiftLeft recurrence for bit blasting -/

/--
Shifts `x` to the left by the first `n` bits of `y`.

The theorem `BitVec.shiftLeft_eq_shiftLeftRec` proves the equivalence of `(x <<< y)` and
`BitVec.shiftLeftRec x y`.

Together with equations `BitVec.shiftLeftRec_zero` and `BitVec.shiftLeftRec_succ`, this allows
`BitVec.shiftLeft` to be unfolded into a circuit for bit blasting.
 -/
def shiftLeftRec (x : BitVec w₁) (y : BitVec w₂) (n : Nat) : BitVec w₁ :=
  let shiftAmt := (y &&& (twoPow w₂ n))
  match n with
  | 0 => x <<< shiftAmt
  | n + 1 => (shiftLeftRec x y n) <<< shiftAmt

@[simp]
theorem shiftLeftRec_zero {x : BitVec w₁} {y : BitVec w₂} :
    shiftLeftRec x y 0 = x <<< (y &&& twoPow w₂ 0)  := by
  simp [shiftLeftRec]

@[simp]
theorem shiftLeftRec_succ {x : BitVec w₁} {y : BitVec w₂} :
    shiftLeftRec x y (n + 1) = (shiftLeftRec x y n) <<< (y &&& twoPow w₂ (n + 1)) := by
  simp [shiftLeftRec]

/--
If `y &&& z = 0`, `x <<< (y ||| z) = x <<< y <<< z`.
This follows as `y &&& z = 0` implies `y ||| z = y + z`,
and thus `x <<< (y ||| z) = x <<< (y + z) = x <<< y <<< z`.
-/
theorem shiftLeft_or_of_and_eq_zero {x : BitVec w₁} {y z : BitVec w₂}
    (h : y &&& z = 0#w₂) :
    x <<< (y ||| z) = x <<< y <<< z := by
  rw [← add_eq_or_of_and_eq_zero _ _ h,
    shiftLeft_eq', toNat_add_of_and_eq_zero h]
  simp [shiftLeft_add]

/--
`shiftLeftRec x y n` shifts `x` to the left by the first `n` bits of `y`.
-/
theorem shiftLeftRec_eq {x : BitVec w₁} {y : BitVec w₂} {n : Nat} :
    shiftLeftRec x y n = x <<< (y.setWidth (n + 1)).setWidth w₂ := by
  induction n generalizing x y
  case zero =>
    ext i
    simp only [shiftLeftRec_zero, twoPow_zero, Nat.reduceAdd, setWidth_one,
      and_one_eq_setWidth_ofBool_getLsbD]
  case succ n ih =>
    simp only [shiftLeftRec_succ, and_twoPow]
    rw [ih]
    by_cases h : y.getLsbD (n + 1)
    · simp only [h, ↓reduceIte]
      rw [setWidth_setWidth_succ_eq_setWidth_setWidth_or_twoPow_of_getLsbD_true h,
        shiftLeft_or_of_and_eq_zero]
      simp [and_twoPow]
    · simp only [h, false_eq_true, ↓reduceIte, shiftLeft_zero']
      rw [setWidth_setWidth_succ_eq_setWidth_setWidth_of_getLsbD_false (i := n + 1)]
      simp [h]

/--
Show that `x <<< y` can be written in terms of `shiftLeftRec`.
This can be unfolded in terms of `shiftLeftRec_zero`, `shiftLeftRec_succ` for bit blasting.
-/
theorem shiftLeft_eq_shiftLeftRec (x : BitVec w₁) (y : BitVec w₂) :
    x <<< y = shiftLeftRec x y (w₂ - 1) := by
  rcases w₂ with rfl | w₂
  · simp [of_length_zero]
  · simp [shiftLeftRec_eq]

/-! # udiv/urem recurrence for bit blasting

In order to prove the correctness of the division algorithm on the integers,
one shows that `n.div d = q` and `n.mod d = r` iff `n = d * q + r` and `0 ≤ r < d`.
Mnemonic: `n` is the numerator, `d` is the denominator, `q` is the quotient, and `r` the remainder.

This *uniqueness of decomposition* is not true for bitvectors.
For `n = 0, d = 3, w = 3`, we can write:
- `0 = 0 * 3 + 0` (`q = 0`, `r = 0 < 3`.)
- `0 = 2 * 3 + 2 = 6 + 2 ≃ 0 (mod 8)` (`q = 2`, `r = 2 < 3`).

Such examples can be created by choosing different `(q, r)` for a fixed `(d, n)`
such that `(d * q + r)` overflows and wraps around to equal `n`.

This tells us that the division algorithm must have more restrictions than just the ones
we have for integers. These restrictions are captured in `DivModState.Lawful`.
The key idea is to state the relationship in terms of the toNat values of {n, d, q, r}.
If the division equation `d.toNat * q.toNat + r.toNat = n.toNat` holds,
then `n.udiv d = q` and `n.umod d = r`.

Following this, we implement the division algorithm by repeated shift-subtract.

References:
- Fast 32-bit Division on the DSP56800E: Minimized nonrestoring division algorithm by David Baca
- Bitwuzla sources for bitblasting.h
-/

private theorem Nat.div_add_eq_left_of_lt {x y z : Nat} (hx : z ∣ x) (hy : y < z) (hz : 0 < z) :
    (x + y) / z = x / z := by
  refine Nat.div_eq_of_lt_le ?lo ?hi
  · apply Nat.le_trans
    · exact div_mul_le_self x z
    · omega
  · simp only [succ_eq_add_one, Nat.add_mul, Nat.one_mul]
    apply Nat.add_lt_add_of_le_of_lt
    · apply Nat.le_of_eq
      exact (Nat.div_eq_iff_eq_mul_left hz hx).mp rfl
    · exact hy

/-- If the division equation `d.toNat * q.toNat + r.toNat = n.toNat` holds,
then `n.udiv d = q`. -/
theorem udiv_eq_of_mul_add_toNat {d n q r : BitVec w} (hd : 0 < d)
    (hrd : r < d)
    (hdqnr : d.toNat * q.toNat + r.toNat = n.toNat) :
    n / d = q := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_udiv]
  replace hdqnr : (d.toNat * q.toNat + r.toNat) / d.toNat = n.toNat / d.toNat := by
    simp [hdqnr]
  rw [Nat.div_add_eq_left_of_lt] at hdqnr
  · rw [← hdqnr]
    exact mul_div_right q.toNat hd
  · exact Nat.dvd_mul_right d.toNat q.toNat
  · exact hrd
  · exact hd

/-- If the division equation `d.toNat * q.toNat + r.toNat = n.toNat` holds,
then `n.umod d = r`. -/
theorem umod_eq_of_mul_add_toNat {d n q r : BitVec w} (hrd : r < d)
    (hdqnr : d.toNat * q.toNat + r.toNat = n.toNat) :
    n % d = r := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_umod]
  replace hdqnr : (d.toNat * q.toNat + r.toNat) % d.toNat = n.toNat % d.toNat := by
    simp [hdqnr]
  rw [Nat.add_mod, Nat.mul_mod_right] at hdqnr
  simp only [Nat.zero_add, mod_mod] at hdqnr
  replace hrd : r.toNat < d.toNat := by
    simpa [BitVec.lt_def] using hrd
  rw [Nat.mod_eq_of_lt hrd] at hdqnr
  simp [hdqnr]

/-! ### DivModState -/

/-- `DivModState` is a structure that maintains the state of recursive `divrem` calls. -/
structure DivModState (w : Nat) : Type where
  /-- The number of bits in the numerator that are not yet processed -/
  wn : Nat
  /-- The number of bits in the remainder (and quotient) -/
  wr : Nat
  /-- The current quotient. -/
  q : BitVec w
  /-- The current remainder. -/
  r : BitVec w


/-- `DivModArgs` contains the arguments to a `divrem` call which remain constant throughout
execution. -/
structure DivModArgs (w : Nat) where
  /-- the numerator (aka, dividend) -/
  n : BitVec w
  /-- the denumerator (aka, divisor)-/
  d : BitVec w

/-- A `DivModState` is lawful if the remainder width `wr` plus the numerator width `wn` equals `w`,
and the bitvectors `r` and `n` have values in the bounds given by bitwidths `wr`, resp. `wn`.

This is a proof engineering choice: an alternative world could have been
`r : BitVec wr` and `n : BitVec wn`, but this required much more dependent typing coercions.

Instead, we choose to declare all involved bitvectors as length `w`, and then prove that
the values are within their respective bounds.

We start with `wn = w` and `wr = 0`, and then in each step, we decrement `wn` and increment `wr`.
In this way, we grow a legal remainder in each loop iteration.
-/
structure DivModState.Lawful {w : Nat} (args : DivModArgs w) (qr : DivModState w) : Prop where
  /-- The sum of widths of the dividend and remainder is `w`. -/
  hwrn : qr.wr + qr.wn = w
  /-- The denominator is positive. -/
  hdPos : 0 < args.d
  /-- The remainder is strictly less than the denominator. -/
  hrLtDivisor : qr.r.toNat < args.d.toNat
  /-- The remainder is morally a `Bitvec wr`, and so has value less than `2^wr`. -/
  hrWidth : qr.r.toNat < 2^qr.wr
  /-- The quotient is morally a `Bitvec wr`, and so has value less than `2^wr`. -/
  hqWidth : qr.q.toNat < 2^qr.wr
  /-- The low `(w - wn)` bits of `n` obey the invariant for division. -/
  hdiv : args.n.toNat >>> qr.wn = args.d.toNat * qr.q.toNat + qr.r.toNat

/-- A lawful DivModState implies `w > 0`. -/
def DivModState.Lawful.hw {args : DivModArgs w} {qr : DivModState w}
    {h : DivModState.Lawful args qr} : 0 < w := by
  have hd := h.hdPos
  rcases w with rfl | w
  · have hcontra : args.d = 0#0 := by apply Subsingleton.elim
    rw [hcontra] at hd
    simp at hd
  · omega

/-- An initial value with both `q, r = 0`. -/
def DivModState.init (w : Nat) : DivModState w := {
  wn := w
  wr := 0
  q := 0#w
  r := 0#w
}

/-- The initial state is lawful. -/
def DivModState.lawful_init {w : Nat} (args : DivModArgs w) (hd : 0#w < args.d) :
    DivModState.Lawful args (DivModState.init w) := by
  simp only [BitVec.DivModState.init]
  exact {
    hwrn := by simp only; omega,
    hdPos := by assumption
    hrLtDivisor := by simp [BitVec.lt_def] at hd ⊢; assumption
    hrWidth := by simp [DivModState.init],
    hqWidth := by simp [DivModState.init],
    hdiv := by
      simp only [DivModState.init, toNat_ofNat, zero_mod, Nat.mul_zero, Nat.add_zero];
      rw [Nat.shiftRight_eq_div_pow]
      apply Nat.div_eq_of_lt args.n.isLt
  }

/--
A lawful DivModState with a fully consumed dividend (`wn = 0`) witnesses that the
quotient has been correctly computed.
-/
theorem DivModState.udiv_eq_of_lawful {n d : BitVec w} {qr : DivModState w}
    (h_lawful : DivModState.Lawful {n, d} qr)
    (h_final  : qr.wn = 0) :
    n / d = qr.q := by
  apply udiv_eq_of_mul_add_toNat h_lawful.hdPos h_lawful.hrLtDivisor
  have hdiv := h_lawful.hdiv
  simp only [h_final] at *
  omega

/--
A lawful DivModState with a fully consumed dividend (`wn = 0`) witnesses that the
remainder has been correctly computed.
-/
theorem DivModState.umod_eq_of_lawful {qr : DivModState w}
    (h : DivModState.Lawful {n, d} qr)
    (h_final  : qr.wn = 0) :
    n % d = qr.r := by
  apply umod_eq_of_mul_add_toNat h.hrLtDivisor
  have hdiv := h.hdiv
  simp only [shiftRight_zero] at hdiv
  simp only [h_final] at *
  exact hdiv.symm

/-! ### DivModState.Poised -/

/--
A `Poised` DivModState is a state which is `Lawful` and furthermore, has at least
one numerator bit left to process `(0 < wn)`

The input to the shift subtractor is a legal input to `divrem`, and we also need to have an
input bit to perform shift subtraction on, and thus we need `0 < wn`.
-/
structure DivModState.Poised {w : Nat} (args : DivModArgs w) (qr : DivModState w)
  extends DivModState.Lawful args qr where
  /-- Only perform a round of shift-subtract if we have dividend bits. -/
  hwn_lt : 0 < qr.wn

/--
In the shift subtract input, the dividend is at least one bit long (`wn > 0`), so
the remainder has bits to be computed (`wr < w`).
-/
def DivModState.wr_lt_w {qr : DivModState w} (h : qr.Poised args) : qr.wr < w := by
  have hwrn := h.hwrn
  have hwn_lt := h.hwn_lt
  omega

/-! ### Division shift subtractor -/

/--
One round of the division algorithm. It tries to perform a subtract shift.

This should only be called when `r.msb = false`, so it will not overflow.
-/
def divSubtractShift (args : DivModArgs w) (qr : DivModState w) : DivModState w :=
  let {n, d} := args
  let wn := qr.wn - 1
  let wr := qr.wr + 1
  let r' := shiftConcat qr.r (n.getLsbD wn)
  if r' < d then {
    q := qr.q.shiftConcat false, -- If `r' < d`, then we do not have a quotient bit.
    r := r'
    wn, wr
  } else {
    q := qr.q.shiftConcat true, -- Otherwise, `r' ≥ d`, and we have a quotient bit.
    r := r' - d -- we subtract to maintain the invariant that `r < d`.
    wn, wr
  }

/-- The value of shifting right by `wn - 1` equals shifting by `wn` and grabbing the lsb at `(wn - 1)`. -/
theorem DivModState.toNat_shiftRight_sub_one_eq
    {args : DivModArgs w} {qr : DivModState w} (h : qr.Poised args) :
    args.n.toNat >>> (qr.wn - 1)
    = (args.n.toNat >>> qr.wn) * 2 + (args.n.getLsbD (qr.wn - 1)).toNat := by
  change BitVec.toNat (args.n >>> (qr.wn - 1)) = _
  have {..} := h -- break the structure down for `omega`
  rw [shiftRight_sub_one_eq_shiftConcat args.n h.hwn_lt]
  rw [toNat_shiftConcat_eq_of_lt (k := w - qr.wn)]
  · simp
  · omega
  · apply BitVec.toNat_ushiftRight_lt
    omega

/--
This is used when proving the correctness of the division algorithm,
where we know that `r < d`.
We then want to show that `((r.shiftConcat b) - d) < d` as the loop invariant.
In arithmetic, this is the same as showing that
`r * 2 + 1 - d < d`, which this theorem establishes.
-/
private theorem two_mul_add_sub_lt_of_lt_of_lt_two (h : a < x) (hy : y < 2) :
    2 * a + y - x < x := by omega

/-- We show that the output of `divSubtractShift` is lawful, which tells us that it
obeys the division equation. -/
theorem lawful_divSubtractShift (qr : DivModState w) (h : qr.Poised args) :
    DivModState.Lawful args (divSubtractShift args qr) := by
  rcases args with ⟨n, d⟩
  simp only [divSubtractShift, decide_eq_true_eq]
  -- We add these hypotheses for `omega` to find them later.
  have ⟨⟨hrwn, hd, hrd, hr, hn, hrnd⟩, hwn_lt⟩ := h
  have : d.toNat * (qr.q.toNat * 2) = d.toNat * qr.q.toNat * 2 := by rw [Nat.mul_assoc]
  by_cases rltd : shiftConcat qr.r (n.getLsbD (qr.wn - 1)) < d
  · simp only [rltd, ↓reduceIte]
    constructor <;> try bv_omega
    case pos.hrWidth => apply toNat_shiftConcat_lt_of_lt <;> omega
    case pos.hqWidth => apply toNat_shiftConcat_lt_of_lt <;> omega
    case pos.hdiv =>
      simp [qr.toNat_shiftRight_sub_one_eq h, h.hdiv, this,
        toNat_shiftConcat_eq_of_lt (qr.wr_lt_w h) h.hrWidth,
        toNat_shiftConcat_eq_of_lt (qr.wr_lt_w h) h.hqWidth]
      omega
  · simp only [rltd, ↓reduceIte]
    constructor <;> try bv_omega
    case neg.hrLtDivisor =>
      simp only [lt_def, Nat.not_lt] at rltd
      rw [BitVec.toNat_sub_of_le rltd,
        toNat_shiftConcat_eq_of_lt (hk := qr.wr_lt_w h) (hx := h.hrWidth),
        Nat.mul_comm]
      apply two_mul_add_sub_lt_of_lt_of_lt_two <;> bv_omega
    case neg.hrWidth =>
      simp only
      have hdr' : d ≤ (qr.r.shiftConcat (n.getLsbD (qr.wn - 1))) :=
        BitVec.not_lt_iff_le.mp rltd
      have hr' : ((qr.r.shiftConcat (n.getLsbD (qr.wn - 1)))).toNat < 2 ^ (qr.wr + 1) := by
        apply toNat_shiftConcat_lt_of_lt <;> bv_omega
      rw [BitVec.toNat_sub_of_le hdr']
      omega
    case neg.hqWidth =>
      apply toNat_shiftConcat_lt_of_lt <;> omega
    case neg.hdiv =>
      have rltd' := (BitVec.not_lt_iff_le.mp rltd)
      simp only [qr.toNat_shiftRight_sub_one_eq h,
        BitVec.toNat_sub_of_le rltd',
        toNat_shiftConcat_eq_of_lt (qr.wr_lt_w h) h.hrWidth]
      simp only [BitVec.le_def,
        toNat_shiftConcat_eq_of_lt (qr.wr_lt_w h) h.hrWidth] at rltd'
      simp only [toNat_shiftConcat_eq_of_lt (qr.wr_lt_w h) h.hqWidth, h.hdiv, Nat.mul_add]
      bv_omega

/-! ### Core division algorithm circuit -/

/-- A recursive definition of division for bit blasting, in terms of a shift-subtraction circuit. -/
@[expose]
def divRec {w : Nat} (m : Nat) (args : DivModArgs w) (qr : DivModState w) :
    DivModState w :=
  match m with
  | 0 => qr
  | m + 1 => divRec m args <| divSubtractShift args qr

@[simp]
theorem divRec_zero (qr : DivModState w) :
    divRec 0 args qr = qr := rfl

@[simp]
theorem divRec_succ (m : Nat) (args : DivModArgs w) (qr : DivModState w) :
    divRec (m + 1) args qr =
      divRec m args (divSubtractShift args qr) := rfl

/-- The output of `divRec` is a lawful state -/
theorem lawful_divRec {args : DivModArgs w} {qr : DivModState w}
    (h : DivModState.Lawful args qr) :
    DivModState.Lawful args (divRec qr.wn args qr) := by
  induction hm : qr.wn generalizing qr with
  | zero =>
    exact h
  | succ wn' ih =>
    simp only [divRec_succ]
    apply ih
    · apply lawful_divSubtractShift
      constructor
      · assumption
      · omega
    · simp only [divSubtractShift, hm]
      split <;> rfl

/-- The output of `divRec` has no more bits left to process (i.e., `wn = 0`) -/
@[simp]
theorem wn_divRec (args : DivModArgs w) (qr : DivModState w) :
    (divRec qr.wn args qr).wn = 0 := by
  induction hm : qr.wn generalizing qr with
  | zero =>
    assumption
  | succ wn' ih =>
    apply ih
    simp only [divSubtractShift, hm]
    split <;> rfl

/-- The result of `udiv` agrees with the result of the division recurrence. -/
theorem udiv_eq_divRec (hd : 0#w < d) :
    let out := divRec w {n, d} (DivModState.init w)
    n / d = out.q := by
  have := DivModState.lawful_init {n, d} hd
  have := lawful_divRec this
  apply DivModState.udiv_eq_of_lawful this (wn_divRec ..)

/-- The result of `umod` agrees with the result of the division recurrence. -/
theorem umod_eq_divRec (hd : 0#w < d) :
    let out := divRec w {n, d} (DivModState.init w)
    n % d = out.r := by
  have := DivModState.lawful_init {n, d} hd
  have := lawful_divRec this
  apply DivModState.umod_eq_of_lawful this (wn_divRec ..)

theorem divRec_succ' (m : Nat) (args : DivModArgs w) (qr : DivModState w) :
    divRec (m+1) args qr =
    let wn := qr.wn - 1
    let wr := qr.wr + 1
    let r' := shiftConcat qr.r (args.n.getLsbD wn)
    let input : DivModState _ :=
      if r' < args.d then {
        q := qr.q.shiftConcat false,
        r := r'
        wn, wr
      } else {
        q := qr.q.shiftConcat true,
        r := r' - args.d
        wn, wr
      }
    divRec m args input := by
  simp [divRec_succ, divSubtractShift]

theorem getElem_udiv (n d : BitVec w) (hy : 0#w < d) (i : Nat) (hi : i < w) :
    (n / d)[i] = (divRec w {n, d} (DivModState.init w)).q[i] := by
  rw [udiv_eq_divRec (by assumption)]

theorem getLsbD_udiv (n d : BitVec w) (hy : 0#w < d)  (i : Nat) :
    (n / d).getLsbD i = (decide (i < w) && (divRec w {n, d} (DivModState.init w)).q.getLsbD i) := by
  by_cases hi : i < w
  · simp [udiv_eq_divRec (by assumption)]
    omega
  · simp_all

theorem getMsbD_udiv (n d : BitVec w) (hd : 0#w < d)  (i : Nat) :
    (n / d).getMsbD i = (decide (i < w) && (divRec w {n, d} (DivModState.init w)).q.getMsbD i) := by
  simp [getMsbD_eq_getLsbD, getLsbD_udiv, udiv_eq_divRec (by assumption)]

/- ### Arithmetic shift right (sshiftRight) recurrence -/

/--
Shifts `x` arithmetically (signed) to the right by the first `n` bits of `y`.

The theorem `BitVec.sshiftRight_eq_sshiftRightRec` proves the equivalence of `(x.sshiftRight y)` and
`BitVec.sshiftRightRec x y`. Together with equations `BitVec.sshiftRightRec_zero`, and
`BitVec.sshiftRightRec_succ`, this allows `BitVec.sshiftRight` to be unfolded into a circuit for
bit blasting.
-/
def sshiftRightRec (x : BitVec w₁) (y : BitVec w₂) (n : Nat) : BitVec w₁ :=
  let shiftAmt := (y &&& (twoPow w₂ n))
  match n with
  | 0 => x.sshiftRight' shiftAmt
  | n + 1 => (sshiftRightRec x y n).sshiftRight' shiftAmt

@[simp]
theorem sshiftRightRec_zero_eq (x : BitVec w₁) (y : BitVec w₂) :
    sshiftRightRec x y 0 = x.sshiftRight' (y &&& twoPow w₂ 0) := by
  simp only [sshiftRightRec]

@[simp]
theorem sshiftRightRec_succ_eq (x : BitVec w₁) (y : BitVec w₂) (n : Nat) :
    sshiftRightRec x y (n + 1) = (sshiftRightRec x y n).sshiftRight' (y &&& twoPow w₂ (n + 1)) := by
  simp [sshiftRightRec]

/--
If `y &&& z = 0`, `x.sshiftRight (y ||| z) = (x.sshiftRight y).sshiftRight z`.
This follows as `y &&& z = 0` implies `y ||| z = y + z`,
and thus `x.sshiftRight (y ||| z) = x.sshiftRight (y + z) = (x.sshiftRight y).sshiftRight z`.
-/
theorem sshiftRight'_or_of_and_eq_zero {x : BitVec w₁} {y z : BitVec w₂}
    (h : y &&& z = 0#w₂) :
    x.sshiftRight' (y ||| z) = (x.sshiftRight' y).sshiftRight' z := by
  simp [sshiftRight', ← add_eq_or_of_and_eq_zero _ _ h,
    toNat_add_of_and_eq_zero h, sshiftRight_add]

theorem sshiftRightRec_eq (x : BitVec w₁) (y : BitVec w₂) (n : Nat) :
    sshiftRightRec x y n = x.sshiftRight' ((y.setWidth (n + 1)).setWidth w₂) := by
  induction n generalizing x y
  case zero =>
    ext i
    simp [twoPow_zero, Nat.reduceAdd, and_one_eq_setWidth_ofBool_getLsbD, setWidth_one]
  case succ n ih =>
    simp only [sshiftRightRec_succ_eq, and_twoPow, ih]
    by_cases h : y.getLsbD (n + 1)
    · rw [setWidth_setWidth_succ_eq_setWidth_setWidth_or_twoPow_of_getLsbD_true h,
        sshiftRight'_or_of_and_eq_zero (by simp [and_twoPow]), h]
      simp
    · rw [setWidth_setWidth_succ_eq_setWidth_setWidth_of_getLsbD_false (i := n + 1)
        (by simp [h])]
      simp [h]

/--
Show that `x.sshiftRight y` can be written in terms of `sshiftRightRec`.
This can be unfolded in terms of `sshiftRightRec_zero_eq`, `sshiftRightRec_succ_eq` for bit blasting.
-/
theorem sshiftRight_eq_sshiftRightRec (x : BitVec w₁) (y : BitVec w₂) :
    (x.sshiftRight' y).getLsbD i = (sshiftRightRec x y (w₂ - 1)).getLsbD i := by
  rcases w₂ with rfl | w₂
  · simp [of_length_zero]
  · simp [sshiftRightRec_eq]

/- ### Logical shift right (ushiftRight) recurrence for bit blasting -/

/--
Shifts `x` logically to the right by the first `n` bits of `y`.

The theorem `BitVec.shiftRight_eq_ushiftRightRec` proves the equivalence
of `(x >>> y)` and `BitVec.ushiftRightRec`.

Together with equations `BitVec.ushiftRightRec_zero` and `BitVec.ushiftRightRec_succ`,
this allows `BitVec.ushiftRight` to be unfolded into a circuit for bit blasting.
-/
def ushiftRightRec (x : BitVec w₁) (y : BitVec w₂) (n : Nat) : BitVec w₁ :=
  let shiftAmt := (y &&& (twoPow w₂ n))
  match n with
  | 0 => x >>> shiftAmt
  | n + 1 => (ushiftRightRec x y n) >>> shiftAmt

@[simp]
theorem ushiftRightRec_zero (x : BitVec w₁) (y : BitVec w₂) :
    ushiftRightRec x y 0 = x >>> (y &&& twoPow w₂ 0) := by
  simp [ushiftRightRec]

@[simp]
theorem ushiftRightRec_succ (x : BitVec w₁) (y : BitVec w₂) :
    ushiftRightRec x y (n + 1) = (ushiftRightRec x y n) >>> (y &&& twoPow w₂ (n + 1)) := by
  simp [ushiftRightRec]

/--
If `y &&& z = 0`, `x >>> (y ||| z) = x >>> y >>> z`.
This follows as `y &&& z = 0` implies `y ||| z = y + z`,
and thus `x >>> (y ||| z) = x >>> (y + z) = x >>> y >>> z`.
-/
theorem ushiftRight'_or_of_and_eq_zero {x : BitVec w₁} {y z : BitVec w₂}
    (h : y &&& z = 0#w₂) :
    x >>> (y ||| z) = x >>> y >>> z := by
  simp [← add_eq_or_of_and_eq_zero _ _ h, toNat_add_of_and_eq_zero h, shiftRight_add]

theorem ushiftRightRec_eq (x : BitVec w₁) (y : BitVec w₂) (n : Nat) :
    ushiftRightRec x y n = x >>> (y.setWidth (n + 1)).setWidth w₂ := by
  induction n generalizing x y
  case zero =>
    ext i
    simp only [ushiftRightRec_zero, twoPow_zero, Nat.reduceAdd,
      and_one_eq_setWidth_ofBool_getLsbD, setWidth_one]
  case succ n ih =>
    simp only [ushiftRightRec_succ, and_twoPow]
    rw [ih]
    by_cases h : y.getLsbD (n + 1) <;> simp only [h, ↓reduceIte]
    · rw [setWidth_setWidth_succ_eq_setWidth_setWidth_or_twoPow_of_getLsbD_true h,
        ushiftRight'_or_of_and_eq_zero]
      simp [and_twoPow]
    · simp [setWidth_setWidth_succ_eq_setWidth_setWidth_of_getLsbD_false, h]

/--
Show that `x >>> y` can be written in terms of `ushiftRightRec`.
This can be unfolded in terms of `ushiftRightRec_zero`, `ushiftRightRec_succ` for bit blasting.
-/
theorem shiftRight_eq_ushiftRightRec (x : BitVec w₁) (y : BitVec w₂) :
    x >>> y = ushiftRightRec x y (w₂ - 1) := by
  rcases w₂ with rfl | w₂
  · simp [of_length_zero]
  · simp [ushiftRightRec_eq]

/-! ### Overflow definitions -/

/-- Unsigned addition overflows iff the final carry bit of the addition circuit is `true`. -/
theorem uaddOverflow_eq {w : Nat} (x y : BitVec w) :
    uaddOverflow x y = (x.setWidth (w + 1) + y.setWidth (w + 1)).msb := by
  simp [uaddOverflow, msb_add, msb_setWidth, carry]

theorem saddOverflow_eq {w : Nat} (x y : BitVec w) :
    saddOverflow x y = (x.msb == y.msb && !((x + y).msb == x.msb)) := by
  simp only [saddOverflow]
  rcases w with _|w
  · revert x y; decide
  · have := le_two_mul_toInt (x := x); have := two_mul_toInt_lt (x := x)
    have := le_two_mul_toInt (x := y); have := two_mul_toInt_lt (x := y)
    simp only [← decide_or, msb_eq_toInt, decide_beq_decide, toInt_add, ← decide_not, ← decide_and,
      decide_eq_decide]
    rw_mod_cast [Int.bmod_neg_iff (by omega) (by omega)]
    simp only [Nat.add_one_sub_one, ge_iff_le]
    omega

theorem usubOverflow_eq {w : Nat} (x y : BitVec w) :
    usubOverflow x y = decide (x < y) := rfl

theorem ssubOverflow_eq {w : Nat} (x y : BitVec w) :
    ssubOverflow x y = ((!x.msb && y.msb && (x - y).msb) || (x.msb && !y.msb && !(x - y).msb)) := by
  simp only [ssubOverflow]
  rcases w with _|w
  · simp [BitVec.of_length_zero]
  · have h₁ := BitVec.toInt_sub_toInt_lt_twoPow_iff (x := x) (y := y)
    have h₂ := BitVec.twoPow_le_toInt_sub_toInt_iff (x := x) (y := y)
    simp only [Nat.add_one_sub_one] at h₁ h₂
    simp only [Nat.add_one_sub_one, ge_iff_le, msb_eq_toInt, ← decide_not, Int.not_lt, toInt_sub]
    simp only [bool_to_prop]
    omega

theorem negOverflow_eq {w : Nat} (x : BitVec w) :
    (negOverflow x) = (decide (0 < w) && (x == intMin w)) := by
  simp only [negOverflow]
  rcases w with _|w
  · simp [toInt_of_zero_length, Int.min_eq_right]
  · suffices - 2 ^ w = (intMin (w + 1)).toInt by simp [beq_eq_decide_eq, ← toInt_inj, this]
    simp only [toInt_intMin, Nat.add_one_sub_one, Int.natCast_emod, Int.neg_inj]
    rw_mod_cast [Nat.mod_eq_of_lt (by simp [Nat.pow_lt_pow_succ])]

/--
  Prove that signed division `x.toInt / y.toInt` only overflows when `x = intMin w` and `y = allOnes w` (for `0 < w`).
-/
theorem sdivOverflow_eq {w : Nat} (x y : BitVec w) :
    (sdivOverflow x y) = (decide (0 < w) && (x = intMin w) && (y = allOnes w)) := by
  rcases w with _|w
  · simp [sdivOverflow, of_length_zero]
  · have yle := le_two_mul_toInt (x := y)
    have ylt := two_mul_toInt_lt (x := y)
    -- if y = allOnes (w + 1), thus y.toInt = -1,
    -- the division overflows iff x = intMin (w + 1), as for negation
    by_cases hy : y = allOnes (w + 1)
    · simp [sdivOverflow_eq_negOverflow_of_eq_allOnes, negOverflow_eq, ← hy, beq_eq_decide_eq]
    · simp only [sdivOverflow, hy, bool_to_prop]
      have := BitVec.neg_two_pow_le_toInt_ediv (x := x) (y := y)
      simp only [Nat.add_one_sub_one] at this
      by_cases hx : 0 ≤ x.toInt
      · by_cases hy' : 0 ≤ y.toInt
        · have := BitVec.toInt_ediv_toInt_lt_of_nonneg_of_nonneg
                (x := x) (y := y) (by omega) (by omega)
          simp only [Nat.add_one_sub_one] at this; simp; omega
        · have := BitVec.toInt_ediv_toInt_nonpos_of_nonneg_of_nonpos
                (x := x) (y := y) (by omega) (by omega)
          simp; omega
      · by_cases hy' : 0 ≤ y.toInt
        · have :=  BitVec.toInt_ediv_toInt_nonpos_of_nonpos_of_nonneg
                (x := x) (y := y) (by omega) (by omega)
          simp; omega
        · have := BitVec.toInt_ediv_toInt_lt_of_nonpos_of_lt_neg_one
                (x := x) (y := y) (by omega) (by rw [← toInt_inj, toInt_allOnes] at hy; omega)
          simp only [Nat.add_one_sub_one] at this; simp; omega

theorem umulOverflow_eq {w : Nat} (x y : BitVec w) :
    umulOverflow x y =
      (0 < w && BitVec.twoPow (w * 2) w ≤ x.zeroExtend (w * 2) * y.zeroExtend (w * 2)) := by
  simp only [umulOverflow, toNat_twoPow, le_def, toNat_mul, toNat_setWidth, mod_mul_mod]
  rcases w with _|w
  · simp [of_length_zero, toInt_zero, mul_mod_mod]
  · simp only [ge_iff_le, show 0 < w + 1 by omega, decide_true, mul_mod_mod, Bool.true_and,
      decide_eq_decide]
    rw [Nat.mod_eq_of_lt BitVec.toNat_mul_toNat_lt, Nat.mod_eq_of_lt]
    have := Nat.pow_lt_pow_of_lt (a := 2) (n := w + 1) (m := (w + 1) * 2)
    omega

theorem smulOverflow_eq {w : Nat} (x y : BitVec w) :
    smulOverflow x y =
      (0 < w &&
      ((signExtend (w * 2) (intMax w)).slt (signExtend (w * 2) x * signExtend (w * 2) y) ||
      (signExtend (w * 2) x * signExtend (w * 2) y).slt (signExtend (w * 2) (intMin w)))) := by
  simp only [smulOverflow]
  rcases w with _|w
  · simp [of_length_zero, toInt_zero]
  · have h₁ := BitVec.two_pow_le_toInt_mul_toInt_iff (x := x) (y := y)
    have h₂ := BitVec.toInt_mul_toInt_lt_neg_two_pow_iff (x := x) (y := y)
    simp only [Nat.add_one_sub_one] at h₁ h₂
    simp [h₁, h₂]

/- ### umod -/

theorem getElem_umod {n d : BitVec w} (hi : i < w) :
    (n % d)[i]
      = if d = 0#w then n[i]
      else (divRec w { n := n, d := d } (DivModState.init w)).r[i] := by
  by_cases hd : d = 0#w
  · simp [hd]
  · have := (BitVec.not_le (x := d) (y := 0#w)).mp
    rw [← BitVec.umod_eq_divRec (by simp [hd, this])]
    simp [hd]

theorem getLsbD_umod {n d : BitVec w}:
    (n % d).getLsbD i
      = if d = 0#w then n.getLsbD i
      else (divRec w { n := n, d := d } (DivModState.init w)).r.getLsbD i := by
  by_cases hi : i < w
  · simp only [BitVec.getLsbD_eq_getElem hi, getElem_umod]
  · simp [show w ≤ i by omega]

theorem getMsbD_umod {n d : BitVec w}:
    (n % d).getMsbD i
      = if d = 0#w then n.getMsbD i
      else (divRec w { n := n, d := d } (DivModState.init w)).r.getMsbD i := by
  by_cases hi : i < w
  · rw [BitVec.getMsbD_eq_getLsbD, getLsbD_umod]
    simp [BitVec.getMsbD_eq_getLsbD, hi]
  · simp [show w ≤ i by omega]


/-! ### Mappings to and from BitVec -/

theorem eq_iff_eq_of_inv (f : α → BitVec w) (g : BitVec w → α) (h : ∀ x, g (f x) = x) :
    ∀ x y, x = y ↔ f x = f y := by
  intro x y
  constructor
  · intro h'
    rw [h']
  · intro h'
    have := congrArg g h'
    simpa [h] using this

@[simp]
theorem ne_intMin_of_lt_of_msb_false {x : BitVec w} (hw : 0 < w) (hx : x.msb = false) :
    x ≠ intMin w := by
  have := toNat_lt_of_msb_false hx
  simp [toNat_eq, Nat.two_pow_pred_mod_two_pow hw]
  omega

@[simp]
theorem ne_zero_of_msb_true {x : BitVec w} (hx : x.msb = true) :
    x ≠ 0#w := by
  have := Nat.two_pow_pos (w-1)
  have := le_toNat_of_msb_true hx
  simp [toNat_eq]
  omega

@[simp]
theorem msb_neg_of_ne_intMin_of_ne_zero {x : BitVec w} (h : x ≠ intMin w) (h' : x ≠ 0#w) :
    (-x).msb = !x.msb := by
  simp only [msb_neg, bool_to_prop]
  simp [h, h']

@[simp]
theorem udiv_intMin_of_msb_false {x : BitVec w} (h : x.msb = false) :
    x / intMin w = 0#w := by
  by_cases hw : w = 0
  · subst hw
    decide +revert
  have wpos : 0 < w := by omega
  have := Nat.two_pow_pos (w-1)
  simp [toNat_eq, wpos]
  exact toNat_lt_of_msb_false h

theorem sdiv_intMin {x : BitVec w} :
    x.sdiv (intMin w) = if x = intMin w then 1#w else 0#w := by
  by_cases hw : w = 0
  · subst hw
    decide +revert
  have wpos : 0 < w := by omega
  by_cases h : x = intMin w
  · subst h
    simp
  · simp only [sdiv_eq, msb_intMin, show 0 < w by omega, h]
    have := Nat.two_pow_pos (w-1)
    by_cases hx : x.msb
    · simp [msb_neg_of_ne_intMin_of_ne_zero (by simp [h])
        (BitVec.ne_zero_of_msb_true hx), hx]
    · simp [hx]

theorem sdiv_neg {x y : BitVec w} (h : y ≠ intMin w) :
    x.sdiv (-y) = -(x.sdiv y) := by
  by_cases h' : y = 0#w
  · subst h'
    simp
  · simp only [BitVec.sdiv, msb_neg_of_ne_intMin_of_ne_zero h (by simp [h'])]
    cases x.msb <;> cases y.msb <;> simp

theorem neg_sdiv {x y : BitVec w} (h : x ≠ intMin w) :
    (-x).sdiv y = -(x.sdiv y) := by
  by_cases hx0 : x = 0#w
  · subst hx0
    simp
  · simp only [BitVec.sdiv, msb_neg_of_ne_intMin_of_ne_zero h (by simp [hx0])]
    cases x.msb <;> cases y.msb <;> simp

theorem neg_sdiv_neg {x y : BitVec w} (h : x ≠ intMin w) :
    (-x).sdiv (-y) = x.sdiv y := by
  by_cases h' : y = intMin w
  · subst h'
    simp [sdiv_intMin, neg_intMin]
  · by_cases hy0 : y = 0#w
    · subst hy0
      simp
    · by_cases hx0 : x = 0#w
      · subst hx0
        simp
      · simp only [BitVec.sdiv,
           msb_neg_of_ne_intMin_of_ne_zero h  (by simp [hx0]),
           msb_neg_of_ne_intMin_of_ne_zero h' (by simp [hy0])]
        cases x.msb <;> cases y.msb <;> simp

theorem intMin_eq_neg_two_pow : intMin w = BitVec.ofInt w (-2 ^ (w - 1)) := by
  apply BitVec.eq_of_toInt_eq
  refine (Nat.eq_zero_or_pos w).elim (by rintro rfl; simp [BitVec.toInt_zero_length]) (fun hw => ?_)
  rw [BitVec.toInt_intMin_of_pos hw, BitVec.toInt_ofInt_eq_self hw (Int.le_refl _)]
  have := Nat.two_pow_pos (w - 1)
  norm_cast
  omega

theorem toInt_intMin_eq_bmod : (intMin w).toInt = (-2 ^ (w - 1)).bmod (2 ^ w) := by
  rw [intMin_eq_neg_two_pow, toInt_ofInt]

@[simp]
theorem toInt_bmod_cancel(b : BitVec w) : b.toInt.bmod (2 ^ w) = b.toInt := by
  rw [toInt_eq_toNat_bmod, Int.bmod_bmod]

theorem sdiv_ne_intMin_of_ne_intMin {x y : BitVec w} (h : x ≠ intMin w) :
    x.sdiv y ≠ intMin w := by
  by_cases hw : w = 0
  · subst hw
    simp [BitVec.eq_nil x] at h
    contradiction
  simp only [sdiv, udiv_eq, neg_eq]
  by_cases hx : x.msb <;> by_cases hy : y.msb
  <;> simp only [hx, hy, neg_ne_intMin_inj]
  <;> simp only [Bool.not_eq_true] at hx hy
  <;> apply ne_intMin_of_lt_of_msb_false (by omega)
  <;> rw [msb_udiv]
  <;> try simp only [hx, Bool.false_and]
  · simp [h, ne_zero_of_msb_true, hx]
  · simp [h, ne_zero_of_msb_true, hx]

theorem toInt_eq_neg_toNat_neg_of_msb_true {x : BitVec w} (h : x.msb = true) :
    x.toInt = -((-x).toNat) := by
  simp only [toInt_eq_msb_cond, h, ↓reduceIte, toNat_neg, Int.natCast_emod]
  norm_cast
  rw [Nat.mod_eq_of_lt]
  · omega
  · have := @BitVec.isLt w x
    have ne_zero := ne_zero_of_msb_true h
    simp only [ne_eq, toNat_eq, toNat_ofNat, zero_mod] at ne_zero
    omega

theorem toInt_eq_neg_toNat_neg_of_nonpos {x : BitVec w} (h : x = 0#w ∨ x.msb = true) :
    x.toInt = -((-x).toNat) := by
  cases h
  case inl h' =>
    simp [h']
  case inr h' =>
    simp [toInt_eq_neg_toNat_neg_of_msb_true h']

theorem intMin_udiv_eq_intMin_iff (x : BitVec w) :
    intMin w / x = intMin w ↔ x = 1#w := by
  by_cases hw : w = 0;   subst hw; decide +revert
  by_cases hx : x = 1#w; subst hx; simp
  have wpos : 0 < w := by omega

  have : 0 ≤ (2 ^ (w - 1) / x.toNat) := by simp
  have := Nat.two_pow_pos (w - 1)

  constructor
  · intro h
    rw [← toInt_inj, toInt_eq_msb_cond] at h
    have : (intMin w / x).msb = false := by simp [msb_udiv, msb_intMin,  wpos, hx]
    simp only [this, false_eq_true, ↓reduceIte, toNat_udiv, toNat_intMin, wpos,
      Nat.two_pow_pred_mod_two_pow, Int.natCast_ediv, toInt_intMin] at h
    omega
  · intro h
    subst h
    simp

theorem intMin_udiv_ne_zero_of_ne_zero {b : BitVec w} (hb : b.msb = false) (hb0 : b ≠ 0#w) :
    intMin w / b ≠ 0#w := by
  by_cases hw : w = 0;   subst hw; decide +revert
  have wpos : 0 < w := by omega

  simp [toNat_eq] at hb0
  have := @Nat.div_eq_zero_iff_lt b.toNat (2 ^ (w-1)) (by omega)
  have := toNat_lt_of_msb_false hb

  simp [toNat_eq, wpos]
  omega

theorem toInt_sdiv_of_ne_or_ne (a b : BitVec w) (h : a ≠ intMin w ∨ b ≠ -1#w) :
    (a.sdiv b).toInt = a.toInt.tdiv b.toInt := by
  by_cases hw0 : w = 0;   subst hw0; decide +revert
  by_cases hw1 : w = 1;   subst hw1; decide +revert
  by_cases ha0 : a = 0#w; subst ha0; simp
  by_cases hb0 : b = 0#w; subst hb0; simp
  by_cases hb1 : b = 1#w; subst hb1; simp [show 1 < w by omega]

  have wpos : 0 < w := by omega
  have := Nat.two_pow_pos (w - 1)

  by_cases hbintMin : b = intMin w
  · simp only [ne_eq, Decidable.not_not] at hbintMin
    subst hbintMin
    have toIntA_lt := @BitVec.toInt_lt w a; norm_cast at toIntA_lt
    have le_toIntA := @BitVec.le_toInt w a; norm_cast at le_toIntA
    simp only [sdiv_intMin, h, ↓reduceIte, toInt_zero, toInt_intMin, wpos,
      Nat.two_pow_pred_mod_two_pow, Int.tdiv_neg]
    · by_cases ha_intMin : a = intMin w
      · simp only [ha_intMin, ↓reduceIte, show 1 < w by omega, toInt_one, toInt_intMin, wpos,
          Nat.two_pow_pred_mod_two_pow, Int.neg_tdiv, Int.neg_neg]
        rw [Int.tdiv_self (by omega)]
      · by_cases ha_nonneg : 0 ≤ a.toInt
        · simp [Int.tdiv_eq_zero_of_lt ha_nonneg (by norm_cast at *), ha_intMin, -Int.natCast_pow]
        · simp only [ne_eq, ← toInt_inj, toInt_intMin, wpos, Nat.two_pow_pred_mod_two_pow] at h
          rw [← Int.neg_tdiv, Int.tdiv_eq_zero_of_lt (by omega)]
          · simp [ha_intMin]
          · simp [wpos, ← toInt_ne, toInt_intMin, -Int.natCast_pow] at ha_intMin
            omega

  · by_cases ha : a.msb <;> by_cases hb : b.msb
    <;> simp only [not_eq_true] at ha hb
    · simp only [sdiv_eq, ha, hb, udiv_eq]
      rw [toInt_eq_neg_toNat_neg_of_nonpos (x := a) (by simp [ha]),
        toInt_eq_neg_toNat_neg_of_nonpos (x := b) (by simp [hb]),
        Int.neg_tdiv_neg, Int.tdiv_eq_ediv_of_nonneg (by omega)]
      rw [toInt_eq_toNat_of_msb]
      · rfl
      · by_cases ha_intMin : a = intMin w
        · simp only [ha_intMin, ne_eq, not_true_eq_false, _root_.false_or] at h
          simp [msb_udiv, neg_eq_iff_eq_neg, h]
        · simp [msb_udiv, ha_intMin, ha]
    · have sdiv_toInt_of_msb_true_of_msb_false :
          (a.sdiv b).toInt = -((-a).toNat / b.toNat) := by
        simp only [sdiv_eq, ha, hb, udiv_eq]
        rw [toInt_eq_neg_toNat_neg_of_nonpos]
        · rw [neg_neg, toNat_udiv, toNat_neg, Int.natCast_emod, Int.neg_inj]
          norm_cast
        · rw [neg_eq_zero_iff]
          by_cases h' : -a / b = 0#w
          · simp [h']
          · by_cases ha_intMin : a = intMin w
            · have ry := (intMin_udiv_eq_intMin_iff b).mp
              simp only [hb1, imp_false] at ry
              simp [msb_udiv, ha_intMin, hb1, ry, intMin_udiv_ne_zero_of_ne_zero, hb, hb0]
            · have := @BitVec.ne_intMin_of_lt_of_msb_false w ((-a) / b) wpos (by simp [ha, ha0, ha_intMin])
              simp [msb_neg, h', this, ha, ha_intMin]
      rw [toInt_eq_toNat_of_msb hb, toInt_eq_neg_toNat_neg_of_msb_true ha, Int.neg_tdiv,
        Int.tdiv_eq_ediv_of_nonneg (by omega), sdiv_toInt_of_msb_true_of_msb_false]
    · rw [← @BitVec.neg_neg w (a.sdiv b), ← sdiv_neg hbintMin]
      have hmb : (-b).msb = false := by simp [hbintMin, hb]
      rw [toInt_neg_of_ne_intMin]
      · simp [sdiv, ha, hmb]
        rw [toInt_udiv_of_msb ha, toInt_eq_toNat_of_msb ha]
        rw [toInt_eq_neg_toNat_neg_of_msb_true hb, Int.tdiv_neg, Int.tdiv_eq_ediv_of_nonneg (by omega)]
      · apply sdiv_ne_intMin_of_ne_intMin
        apply ne_intMin_of_lt_of_msb_false (by omega) ha
    · rw [sdiv, Int.tdiv_cases, udiv_eq, neg_eq, if_pos (toInt_nonneg_of_msb_false ha),
        if_pos (toInt_nonneg_of_msb_false hb), ha, hb, toInt_udiv_of_msb ha,
        toInt_eq_toNat_of_msb ha, toInt_eq_toNat_of_msb hb]

theorem intMin_sdiv_neg_one : (intMin w).sdiv (-1#w) = intMin w := by
  refine (Nat.eq_zero_or_pos w).elim (by rintro rfl; exact Subsingleton.elim _ _) (fun hw => ?_)
  apply BitVec.eq_of_toNat_eq
  rw [sdiv]
  simp [msb_intMin, hw, neg_one_eq_allOnes, msb_allOnes]
  have : 2 ≤ 2 ^ w := Nat.pow_one 2 ▸ (Nat.pow_le_pow_iff_right (by omega)).2 (by omega)
  rw [Nat.sub_sub_self (by omega), Nat.mod_eq_of_lt, Nat.div_one]
  omega

theorem toInt_sdiv (a b : BitVec w) : (a.sdiv b).toInt = (a.toInt.tdiv b.toInt).bmod (2 ^ w) := by
  by_cases h : a = intMin w ∧ b = -1#w
  · rcases h with ⟨rfl, rfl⟩
    rw [BitVec.intMin_sdiv_neg_one]
    refine (Nat.eq_zero_or_pos w).elim (by rintro rfl; simp [toInt_of_zero_length]) (fun hw => ?_)
    rw [toInt_intMin_of_pos hw, neg_one_eq_allOnes, toInt_allOnes, if_pos hw, Int.tdiv_neg,
      Int.tdiv_one, Int.neg_neg, Int.bmod_eq_neg (Int.pow_nonneg (by omega))]
    conv => lhs; rw [(by omega: w = (w - 1) + 1)]
    simp [Nat.pow_succ, Int.natCast_pow, Int.mul_comm]
  · rw [← toInt_bmod_cancel]
    rw [BitVec.toInt_sdiv_of_ne_or_ne _ _ (by simpa only [Decidable.not_and_iff_not_or_not] using h)]

theorem msb_umod_eq_false_of_left {x : BitVec w} (hx : x.msb = false) (y : BitVec w) : (x % y).msb = false := by
  rw [msb_eq_false_iff_two_mul_lt] at hx ⊢
  rw [toNat_umod]
  refine Nat.lt_of_le_of_lt ?_ hx
  rw [Nat.mul_le_mul_left_iff (by decide)]
  exact Nat.mod_le _ _

theorem msb_umod_of_le_of_ne_zero_of_le {x y : BitVec w}
    (hx : x ≤ intMin w) (hy : y ≠ 0#w) (hy' : y ≤ intMin w) : (x % y).msb = false := by
  simp only [msb_umod, Bool.and_eq_false_imp, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    BitVec.not_lt, beq_eq_false_iff_ne, ne_eq, hy, not_false_eq_true, _root_.and_true]
  intro h
  rw [← intMin_le_iff_msb_eq_true (length_pos_of_ne hy)] at h
  rwa [BitVec.le_antisymm hx h]

@[simp]
theorem toInt_srem (x y : BitVec w) : (x.srem y).toInt = x.toInt.tmod y.toInt := by
  rw [srem_eq]
  by_cases hyz : y = 0#w
  · simp only [hyz, ofNat_eq_ofNat, msb_zero, umod_zero, neg_zero, neg_neg, toInt_zero, Int.tmod_zero]
    cases x.msb <;> rfl
  cases h : x.msb
  · cases h' : y.msb
    · dsimp only
      rw [toInt_eq_toNat_of_msb (msb_umod_eq_false_of_left h y), toNat_umod]
      rw [toInt_eq_toNat_of_msb h, toInt_eq_toNat_of_msb h', ← Int.ofNat_tmod]
    · dsimp only
      rw [toInt_eq_toNat_of_msb (msb_umod_eq_false_of_left h _), toNat_umod]
      rw [toInt_eq_toNat_of_msb h, toInt_eq_neg_toNat_neg_of_msb_true h']
      rw [Int.tmod_neg, ← Int.ofNat_tmod]
  · cases h' : y.msb
    · dsimp only
      rw [toInt_eq_neg_toNat_neg_of_msb_true h, toInt_eq_toNat_of_msb h', Int.neg_tmod]
      rw [← Int.ofNat_tmod, ← toNat_umod, toInt_neg_eq_of_msb ?msb, toInt_eq_toNat_of_msb ?msb]
      rw [BitVec.msb_umod_of_le_of_ne_zero_of_le (neg_le_intMin_of_msb_eq_true h) hyz]
      exact le_intMin_of_msb_eq_false h'
    · dsimp only
      rw [toInt_eq_neg_toNat_neg_of_msb_true h, toInt_eq_neg_toNat_neg_of_msb_true h', Int.neg_tmod, Int.tmod_neg]
      rw [← Int.ofNat_tmod, ← toNat_umod, toInt_neg_eq_of_msb ?msb', toInt_eq_toNat_of_msb ?msb']
      rw [BitVec.msb_umod_of_le_of_ne_zero_of_le (neg_le_intMin_of_msb_eq_true h)
        ((not_congr neg_eq_zero_iff).mpr hyz)]
      exact neg_le_intMin_of_msb_eq_true h'

@[simp]
theorem msb_intMin_umod_neg_of_msb_true {y : BitVec w} (hy : y.msb = true) :
    (intMin w % -y).msb = false := by
  by_cases hyintmin : y = intMin w
  · simp [hyintmin]
  · rw [msb_umod_of_msb_false_of_ne_zero (by simp [hyintmin, hy])]
    simp [hy]

@[simp]
theorem msb_neg_umod_neg_of_msb_true_of_msb_true {x y : BitVec w} (hx : x.msb = true) (hy : y.msb = true) :
      (-x % -y).msb = false := by
  by_cases hx' : x = intMin w
  · simp only [hx', neg_intMin, msb_intMin_umod_neg_of_msb_true hy]
  · simp [show (-x).msb = false by simp [hx, hx']]

theorem toInt_dvd_toInt_iff {x y : BitVec w} :
    y.toInt ∣ x.toInt ↔ (if x.msb then -x else x) % (if y.msb then -y else y) = 0#w := by
  constructor
  <;> by_cases hxmsb : x.msb <;> by_cases hymsb: y.msb
  <;> intros h
  <;> simp only [hxmsb, hymsb, reduceIte, false_eq_true, toNat_eq, toNat_umod, toNat_ofNat,
        zero_mod, toInt_eq_neg_toNat_neg_of_msb_true, Int.dvd_neg, Int.neg_dvd,
        toInt_eq_toNat_of_msb] at h
  <;> simp only [hxmsb, hymsb, toInt_eq_neg_toNat_neg_of_msb_true, toInt_eq_toNat_of_msb,
        Int.dvd_neg, Int.neg_dvd, toNat_eq, toNat_umod, reduceIte, toNat_ofNat, zero_mod]
  <;> norm_cast
  <;> norm_cast at h
  <;> simp only [dvd_of_mod_eq_zero, h, dvd_iff_mod_eq_zero.mp, reduceIte]

theorem toInt_dvd_toInt_iff_of_msb_true_msb_false {x y : BitVec w} (hx : x.msb = true) (hy : y.msb = false) :
    y.toInt ∣ x.toInt ↔ (-x) % y = 0#w := by
  simpa [hx, hy] using toInt_dvd_toInt_iff (x := x) (y := y)

theorem toInt_dvd_toInt_iff_of_msb_false_msb_true {x y : BitVec w} (hx : x.msb = false) (hy : y.msb = true) :
    y.toInt ∣ x.toInt ↔ x % (-y) = 0#w := by
  simpa [hx, hy] using toInt_dvd_toInt_iff (x := x) (y := y)

@[simp]
theorem neg_toInt_neg_umod_eq_of_msb_true_msb_true {x y : BitVec w} (hx : x.msb = true) (hy : y.msb = true) :
    -(-(-x % -y)).toInt = (-x % -y).toNat := by
  rw [neg_toInt_neg]
  by_cases h : -x % -y = 0#w
  · simp [h]
  · rw [msb_neg_umod_neg_of_msb_true_of_msb_true hx hy]

@[simp]
theorem toInt_umod_neg_add {x y : BitVec w} (hymsb : y.msb = true) (hxmsb : x.msb = false) (hdvd : ¬y.toInt ∣ x.toInt) :
    (x % -y + y).toInt = x.toInt % y.toInt + y.toInt := by
  rcases w with _|w ; simp [of_length_zero]
  have hypos : 0 < y.toNat := toNat_pos_of_ne_zero (by simp [hymsb])
  have hxnonneg := toInt_nonneg_of_msb_false hxmsb
  have hynonpos := toInt_neg_of_msb_true hymsb
  have hylt : (-y).toNat ≤ 2 ^ (w) := toNat_neg_lt_of_msb y hymsb
  have hmodlt := Nat.mod_lt x.toNat (y := (-y).toNat)
      (by rw [toNat_neg, Nat.mod_eq_of_lt (by omega)]; omega)
  simp only [hdvd, reduceIte, toInt_add, hxnonneg, show ¬0 ≤ y.toInt by omega]
  rw [toInt_umod, toInt_eq_neg_toNat_neg_of_msb_true hymsb, Int.bmod_add_bmod,
    Int.bmod_eq_of_le (by omega) (by omega),
    toInt_eq_toNat_of_msb hxmsb, Int.emod_neg]

@[simp]
theorem toInt_sub_neg_umod {x y : BitVec w} (hxmsb : x.msb = true) (hymsb : y.msb = false) (hdvd : ¬y.toInt ∣ x.toInt) :
    (y - -x % y).toInt = x.toInt % y.toInt := by
  rcases w with _|w
  · simp [of_length_zero]
  · have : y.toNat < 2 ^ w := toNat_lt_of_msb_false hymsb
    by_cases hyzero : y = 0#(w+1)
    · subst hyzero; simp
    · simp only [toNat_eq, toNat_ofNat, zero_mod] at hyzero
      have hypos : 0 < y.toNat := by omega
      simp only [reduceIte, toInt_sub, toInt_eq_toNat_of_msb hymsb, toInt_umod,
        Int.sub_bmod_bmod, toInt_eq_neg_toNat_neg_of_msb_true hxmsb, Int.neg_emod]
      have hmodlt := Nat.mod_lt (x := (-x).toNat) (y := y.toNat) hypos
      rw [Int.bmod_eq_of_le (by omega) (by omega)]
      simp only [toInt_eq_toNat_of_msb hymsb, BitVec.toInt_eq_neg_toNat_neg_of_msb_true hxmsb,
        Int.dvd_neg] at hdvd
      simp only [hdvd, ↓reduceIte, Int.natAbs_cast]

theorem toInt_smod {x y : BitVec w} :
    (x.smod y).toInt = x.toInt.fmod y.toInt := by
  rcases w with _|w
  · decide +revert
  · by_cases hyzero : y = 0#(w + 1)
    · simp [hyzero]
    · rw [smod_eq]
      cases hxmsb : x.msb <;> cases hymsb : y.msb
      <;> simp only [umod_eq]
      · have : 0 < y.toNat := by simp [toNat_eq] at hyzero; omega
        have : y.toNat < 2 ^ w := toNat_lt_of_msb_false hymsb
        have : x.toNat % y.toNat < y.toNat := Nat.mod_lt x.toNat (by omega)
        rw [toInt_umod, Int.fmod_eq_emod_of_nonneg x.toInt (toInt_nonneg_of_msb_false hymsb),
          toInt_eq_toNat_of_msb hxmsb, toInt_eq_toNat_of_msb hymsb,
          Int.bmod_eq_of_le_mul_two (by omega) (by omega)]
      · have := toInt_dvd_toInt_iff_of_msb_false_msb_true hxmsb hymsb
        by_cases hx_dvd_y : y.toInt ∣ x.toInt
        · simp [show x % -y = 0#(w + 1) by simp_all, hx_dvd_y, Int.fmod_eq_zero_of_dvd]
        · have hynonpos := toInt_neg_of_msb_true hymsb
          simp only [show ¬x % -y = 0#(w + 1) by simp_all, ↓reduceIte,
            toInt_umod_neg_add hymsb hxmsb hx_dvd_y, Int.fmod_eq_emod, show ¬0 ≤ y.toInt by omega,
            hx_dvd_y, _root_.or_self]
      · have hynonneg := toInt_nonneg_of_msb_false hymsb
        rw [Int.fmod_eq_emod_of_nonneg x.toInt (b := y.toInt) (by omega)]
        have hdvd := toInt_dvd_toInt_iff_of_msb_true_msb_false hxmsb hymsb
        by_cases hx_dvd_y : y.toInt ∣ x.toInt
        · simp [show -x % y = 0#(w + 1) by simp_all, hx_dvd_y, Int.emod_eq_zero_of_dvd]
        · simp [show ¬-x % y = 0#(w + 1) by simp_all, toInt_sub_neg_umod hxmsb hymsb hx_dvd_y]
      · rw [←Int.neg_inj, neg_toInt_neg_umod_eq_of_msb_true_msb_true hxmsb hymsb]
        simp [BitVec.toInt_eq_neg_toNat_neg_of_msb_true, hxmsb, hymsb,
          Int.fmod_eq_emod_of_nonneg _, show 0 ≤ (-y).toNat by omega]

/-! ### Lemmas that use bit blasting circuits -/

theorem add_sub_comm {x y : BitVec w} : x + y - z = x - z + y := by
  apply eq_of_toNat_eq
  simp only [toNat_sub, toNat_add, add_mod_mod, mod_add_mod]
  congr 1
  omega

theorem sub_add_comm {x y : BitVec w} : x - y + z = x + z - y := by
  rw [add_sub_comm]

theorem not_add_one {x : BitVec w} : ~~~ (x + 1#w) = ~~~ x - 1#w := by
  rw [not_eq_neg_add, not_eq_neg_add, neg_add]

theorem not_add_eq_not_neg {x y : BitVec w} : ~~~ (x + y) = ~~~ x - y := by
  rw [not_eq_neg_add, not_eq_neg_add, neg_add]
  simp only [sub_eq_add_neg]
  rw [BitVec.add_assoc, @BitVec.add_comm _ (-y), ← BitVec.add_assoc]

theorem not_sub_one_eq_not_add_one {x : BitVec w} : ~~~ (x - 1#w) = ~~~ x + 1#w := by
  rw [not_eq_neg_add, not_eq_neg_add, neg_sub,
    BitVec.add_sub_cancel, BitVec.sub_add_cancel]

theorem not_sub_eq_not_add {x y : BitVec w} : ~~~ (x - y) = ~~~ x + y := by
  rw [BitVec.sub_eq_add_neg, not_add_eq_not_neg, sub_neg]

/-- The value of `(carry i x y false)` can be computed by truncating `x` and `y`
to `len` bits where `len ≥ i`. -/
theorem carry_extractLsb'_eq_carry {w i len : Nat} (hi : i < len)
    {x y : BitVec w} {b : Bool}:
    (carry i (extractLsb' 0 len x) (extractLsb' 0 len y) b)
    = (carry i x y b) := by
  simp only [carry, extractLsb'_toNat, shiftRight_zero, toNat_false, Nat.add_zero, ge_iff_le,
    decide_eq_decide]
  have : 2 ^ i ∣ 2^len := by
    apply Nat.pow_dvd_pow
    omega
  rw [Nat.mod_mod_of_dvd _ this, Nat.mod_mod_of_dvd _ this]

/--
The `[0..len)` low bits of `x + y` can be computed by truncating `x` and `y`
to `len` bits and then adding.
-/
theorem extractLsb'_add {w len : Nat} {x y : BitVec w} (hlen : len ≤ w) :
    (x + y).extractLsb' 0 len = x.extractLsb' 0 len + y.extractLsb' 0 len := by
  ext i hi
  rw [getElem_extractLsb', Nat.zero_add, getLsbD_add (by omega)]
  simp [getElem_add, carry_extractLsb'_eq_carry hi, getElem_extractLsb', Nat.zero_add]

/-- `extractLsb'` commutes with multiplication. -/
theorem extractLsb'_mul {w len} {x y : BitVec w} (hlen : len ≤ w) :
    (x * y).extractLsb' 0 len = (x.extractLsb' 0 len) * (y.extractLsb' 0 len) := by
  simp [← setWidth_eq_extractLsb' hlen, setWidth_mul _ _ hlen]

/-- Adding bitvectors that are zero in complementary positions equals concatenation.
We add a `no_index` annotation to `HAppend.hAppend` such that the width `v + w`
does not act as a key in the discrimination tree.
This is important to allow matching, when the type of the result of append
`x : BitVec 3` and `y : BitVec 4` has been reduced to `x ++ y : BitVec 7`.
-/
theorem append_zero_add_zero_append {v w : Nat} {x : BitVec v} {y : BitVec w} :
    (HAppend.hAppend (γ := BitVec (no_index _)) x 0#w) +
    (HAppend.hAppend (γ := BitVec (no_index _)) 0#v y)
    = x ++ y := by
  rw [add_eq_or_of_and_eq_zero] <;> ext i <;> simp

/-- Adding bitvectors that are zero in complementary positions equals concatenation. -/
theorem zero_append_add_append_zero {v w : Nat} {x : BitVec v} {y : BitVec w} :
  (HAppend.hAppend (γ := BitVec (no_index _)) 0#v y) +
  (HAppend.hAppend (γ := BitVec (no_index _)) x 0#w)
  = x ++ y := by
  rw [add_eq_or_of_and_eq_zero] <;> ext i <;> simp

/-- Heuristically, `y <<< x` is much larger than `x`,
and hence low bits of `y <<< x`. Thus, `x + (y <<< x) = x ||| (y <<< x).` -/
theorem add_shiftLeft_eq_or_shiftLeft {x y : BitVec w} :
    x + (y <<< x) =  x ||| (y <<< x) := by
  rw [add_eq_or_of_and_eq_zero]
  ext i hi
  simp only [shiftLeft_eq', getElem_and, getElem_shiftLeft, getElem_zero, and_eq_false_imp,
    not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Nat.not_lt]
  intros hxi hxval
  have : 2^i ≤ x.toNat := two_pow_le_toNat_of_getElem_eq_true hi hxi
  have : i < 2^i := by exact Nat.lt_two_pow_self
  omega

/-- Heuristically, `y <<< x` is much larger than `x`,
and hence low bits of `y <<< x`. Thus, `(y <<< x) + x = (y <<< x) ||| x.` -/
theorem shiftLeft_add_eq_shiftLeft_or {x y : BitVec w} :
    (y <<< x) + x =  (y <<< x) ||| x := by
  rw [BitVec.add_comm, add_shiftLeft_eq_or_shiftLeft, or_comm]

end BitVec
