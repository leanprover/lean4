/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix
-/

prelude
import Init.Data.Bool
import Init.Data.Int.Pow
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Lemmas
import Init.TacticsExtra
import Init.Omega

/-
This module defines properties of the bitwise operations on Natural numbers.

It is primarily intended to support the bitvector library.
-/


namespace Nat

@[local simp]
private theorem one_div_two : 1/2 = 0 := by trivial

private theorem decide_mod_two_eq_one {x : Nat} : decide (x % 2 = 1) = (x % 2 != 0) := by
  cases mod_two_eq_zero_or_one x with | _ h => simp (config := {decide := true}) [h]

private theorem two_pow_succ_sub_succ_div_two : (2 ^ (n+1) - (x + 1)) / 2 = 2^n - (x/2 + 1) := by
  omega

private theorem two_pow_succ_sub_one_div_two : (2 ^ (n+1) - 1) / 2 = 2^n - 1 :=
  two_pow_succ_sub_succ_div_two

private theorem two_mul_sub_one {n : Nat} (n_pos : n > 0) : (2*n - 1) % 2 = 1 := by
  omega

/-! ### Preliminaries -/

@[simp] theorem zero_and (x : Nat) : 0 &&& x = 0 := by rfl

@[simp] theorem and_zero (x : Nat) : x &&& 0 = 0 := by
  simp only [HAnd.hAnd, AndOp.and, land]
  unfold bitwise
  simp

@[simp] theorem one_and_is_mod (x : Nat) : 1 &&& x = x % 2 := by
  if xz : x = 0 then
    simp [xz, zero_and]
  else
    have zand := zero_and (x/2)
    simp only [HAnd.hAnd, AndOp.and, land] at zand ⊢
    unfold bitwise
    cases mod_two_eq_zero_or_one x with | _ p => simp [xz, p, zand]

/-! ### testBit' -/

@[simp] theorem zero_testBit' (i : Nat) : testBit' 0 i = false := by
  simp only [testBit', zero_shiftRight, bodd, and_zero, bne_self_eq_false]

@[simp] theorem testBit'_zero (x : Nat) : testBit' x 0 = bodd x :=
  rfl

@[simp] theorem testBit'_succ (x i : Nat) : testBit' x (i + 1) = testBit' (x / 2) i := by
  unfold testBit'
  simp [shiftRight_succ_inside, div2]

theorem testBit'_to_div_mod {x : Nat} : testBit' x i = decide (x / 2^i % 2 = 1) := by
  induction i generalizing x with
  | zero =>
    unfold testBit'
    cases mod_two_eq_zero_or_one x with | _ xz => simp [bodd, xz]
  | succ i hyp =>
    simp [hyp, Nat.div_div_eq_div_mul, Nat.pow_succ']

theorem toNat_testBit' (x i : Nat) :
    (x.testBit' i).toNat = x / 2 ^ i % 2 := by
  rw [Nat.testBit'_to_div_mod]
  rcases Nat.mod_two_eq_zero_or_one (x / 2^i) <;> simp_all

theorem ne_zero_implies_bit_true {x : Nat} (xnz : x ≠ 0) : ∃ i, testBit' x i := by
  induction x using binaryRecFromOne with
  | z₀ => exact absurd rfl xnz
  | z₁ => exact ⟨0, rfl⟩
  | f b n n0 hyp =>
    obtain ⟨i, h⟩ := hyp n0
    refine ⟨i + 1, ?_⟩
    rwa [testBit'_succ, bit_div_two]

theorem ne_implies_bit_diff {x y : Nat} (p : x ≠ y) : ∃ i, testBit' x i ≠ testBit' y i := by
  induction y using binaryRec' generalizing x with
  | z =>
    simp only [zero_testBit', Bool.ne_false_iff]
    exact ne_zero_implies_bit_true p
  | f yb y h hyp =>
    rw [← x.bit_decomp] at *
    by_cases hb : bodd x = yb
    · subst hb
      obtain ⟨i, h⟩ := hyp (mt (congrArg _) p)
      refine ⟨i + 1, ?_⟩
      rwa [testBit'_succ, bit_div_two, testBit'_succ, bit_div_two]
    · refine ⟨0, ?_⟩
      rwa [testBit'_zero, testBit'_zero, bodd_bit, bodd_bit]

/--
`eq_of_testBit'_eq` allows proving two natural numbers are equal
if their bits are all equal.
-/
theorem eq_of_testBit'_eq {x y : Nat} (pred : ∀i, testBit' x i = testBit' y i) : x = y := by
  if h : x = y then
    exact h
  else
    let ⟨i,eq⟩ := ne_implies_bit_diff h
    have p := pred i
    contradiction

theorem ge_two_pow_implies_high_bit_true {x : Nat} (p : 2^n ≤ x) : ∃ i, n ≤ i ∧ testBit' x i := by
  induction x using binaryRec generalizing n with
  | z => exact absurd p (Nat.not_le_of_lt n.two_pow_pos)
  | f xb x hyp =>
    match n with
    | 0 =>
      simp only [zero_le, true_and]
      exact ne_zero_implies_bit_true (ne_of_gt (Nat.lt_of_succ_le p))
    | n+1 =>
      obtain ⟨i, h⟩ := hyp (mul_two_le_bit.mp p)
      refine ⟨i + 1, ?_⟩
      rwa [Nat.add_le_add_iff_right, testBit'_succ, bit_div_two]

theorem testBit'_implies_ge {x : Nat} (p : testBit' x i = true) : x ≥ 2^i := by
  simp only [testBit'_to_div_mod] at p
  apply Decidable.by_contra
  intro not_ge
  have x_lt : x < 2^i := Nat.lt_of_not_le not_ge
  simp [div_eq_of_lt x_lt] at p

theorem testBit'_lt_two_pow {x i : Nat} (lt : x < 2^i) : x.testBit' i = false := by
  match p : x.testBit' i with
  | false => trivial
  | true =>
    exfalso
    exact Nat.not_le_of_gt lt (testBit'_implies_ge p)

theorem lt_pow_two_of_testBit' (x : Nat) (p : ∀i, i ≥ n → testBit' x i = false) : x < 2^n := by
  apply Decidable.by_contra
  intro not_lt
  have x_ge_n := Nat.ge_of_not_lt not_lt
  have ⟨i, ⟨i_ge_n, test_true⟩⟩ := ge_two_pow_implies_high_bit_true x_ge_n
  have test_false := p _ i_ge_n
  simp only [test_true] at test_false

/-! ### testBit' -/

private theorem succ_mod_two : succ x % 2 = 1 - x % 2 := by
  induction x with
  | zero =>
    trivial
  | succ x hyp =>
    have p : 2 ≤ x + 2 := Nat.le_add_left _ _
    simp [Nat.mod_eq (x+2) 2, p, hyp]
    cases Nat.mod_two_eq_zero_or_one x with | _ p => simp [p]

private theorem testBit'_succ_zero : testBit' (x + 1) 0 = not (testBit' x 0) := by
  simp [testBit'_to_div_mod, succ_mod_two]
  cases Nat.mod_two_eq_zero_or_one x with | _ p =>
    simp [p]

theorem testBit'_two_pow_add_eq (x i : Nat) : testBit' (2^i + x) i = not (testBit' x i) := by
  simp [testBit'_to_div_mod, add_div_left, Nat.two_pow_pos, succ_mod_two]
  cases mod_two_eq_zero_or_one (x / 2 ^ i) with
  | _ p => simp [p]

theorem testBit'_mul_two_pow_add_eq (a b i : Nat) :
    testBit' (2^i*a + b) i = Bool.xor (a%2 = 1) (testBit' b i) := by
  match a with
  | 0 => simp
  | a+1 =>
    simp [Nat.mul_succ, Nat.add_assoc,
          testBit'_mul_two_pow_add_eq a,
          testBit'_two_pow_add_eq,
          Nat.succ_mod_two]
    cases mod_two_eq_zero_or_one a with
    | _ p => simp [p]

theorem testBit'_two_pow_add_gt {i j : Nat} (j_lt_i : j < i) (x : Nat) :
    testBit' (2^i + x) j = testBit' x j := by
  have i_def : i = j + (i-j) := (Nat.add_sub_cancel' (Nat.le_of_lt j_lt_i)).symm
  rw [i_def]
  simp only [testBit'_to_div_mod, Nat.pow_add,
        Nat.add_comm x, Nat.mul_add_div (Nat.two_pow_pos _)]
  match i_sub_j_eq : i - j with
  | 0 =>
    exfalso
    rw [Nat.sub_eq_zero_iff_le] at i_sub_j_eq
    exact Nat.not_le_of_gt j_lt_i i_sub_j_eq
  | d+1 =>
    simp [Nat.pow_succ, Nat.mul_comm _ 2, Nat.mul_add_mod]

@[simp] theorem testBit'_mod_two_pow (x j i : Nat) :
    testBit' (x % 2^j) i = (decide (i < j) && testBit' x i) := by
  induction x using Nat.strongInductionOn generalizing j i with
  | ind x hyp =>
    rw [mod_eq]
    rcases Nat.lt_or_ge x (2^j) with x_lt_j | x_ge_j
    · have not_j_le_x := Nat.not_le_of_gt x_lt_j
      simp [not_j_le_x]
      rcases Nat.lt_or_ge i j with i_lt_j | i_ge_j
      · simp [i_lt_j]
      · have x_lt : x < 2^i :=
            calc x < 2^j := x_lt_j
                _ ≤ 2^i := Nat.pow_le_pow_of_le_right Nat.zero_lt_two i_ge_j
        simp [Nat.testBit'_lt_two_pow x_lt]
    · generalize y_eq : x - 2^j = y
      have x_eq : x = y + 2^j := Nat.eq_add_of_sub_eq x_ge_j y_eq
      simp only [Nat.two_pow_pos, x_eq, Nat.le_add_left, true_and, ite_true]
      have y_lt_x : y < x := by
            simp [x_eq]
            exact Nat.lt_add_of_pos_right (Nat.two_pow_pos j)
      simp only [hyp y y_lt_x]
      if i_lt_j : i < j then
        rw [ Nat.add_comm _ (2^_), testBit'_two_pow_add_gt i_lt_j]
      else
        simp [i_lt_j]

theorem testBit'_one_zero : testBit' 1 0 = true := by trivial

theorem not_decide_mod_two_eq_one (x : Nat)
    : (!decide (x % 2 = 1)) = decide (x % 2 = 0) := by
  cases Nat.mod_two_eq_zero_or_one x <;> (rename_i p; simp [p])

theorem testBit'_two_pow_sub_succ (h₂ : x < 2 ^ n) (i : Nat) :
    testBit' (2^n - (x + 1)) i = (decide (i < n) && ! testBit' x i) := by
  induction i generalizing n x with
  | zero =>
    match n with
    | 0 => simp
    | n+1 =>
      simp [not_decide_mod_two_eq_one, Nat.bodd]
      omega
  | succ i ih =>
    simp only [testBit'_succ]
    match n with
    | 0 =>
      simp [decide_eq_false]
    | n+1 =>
      rw [Nat.two_pow_succ_sub_succ_div_two, ih]
      · simp [Nat.succ_lt_succ_iff]
      · omega

@[simp] theorem testBit'_two_pow_sub_one (n i : Nat) : testBit' (2^n-1) i = decide (i < n) := by
  rw [testBit'_two_pow_sub_succ]
  · simp
  · exact Nat.two_pow_pos _

theorem testBit'_bool_to_nat (b : Bool) (i : Nat) :
    testBit' (Bool.toNat b) i = (decide (i = 0) && b) := by
  cases b <;> cases i <;>
  simp [testBit'_to_div_mod, Nat.pow_succ, Nat.mul_comm _ 2,
        ←Nat.div_div_eq_div_mul _ 2, one_div_two,
        Nat.mod_eq_of_lt]

/-! ### bitwise -/

theorem testBit'_bitwise
  (false_false_axiom : f false false = false) (x y i : Nat)
: (bitwise f x y).testBit' i = f (x.testBit' i) (y.testBit' i) := by
  induction i using Nat.strongInductionOn generalizing x y with
  | ind i hyp =>
    unfold bitwise
    if x_zero : x = 0 then
      cases p : f false true <;>
        cases yi : testBit' y i <;>
          simp [x_zero, p, yi, false_false_axiom]
    else if y_zero : y = 0 then
      simp [x_zero, y_zero]
      cases p : f true false <;>
        cases xi : testBit' x i <;>
          simp [p, xi, false_false_axiom]
    else
      simp only [x_zero, y_zero, ←Nat.two_mul]
      cases i with
      | zero =>
        cases p : f (x % 2 != 0) (y % 2 != 0) <;>
          simp [p, testBit'_zero, bodd, decide_mod_two_eq_one, Nat.mul_add_mod]
      | succ i =>
        have hyp_i := hyp i (Nat.le_refl (i+1))
        cases p : f (x % 2 != 0) (y % 2 != 0) <;>
          simp [p, testBit'_succ, decide_mod_two_eq_one, hyp_i, Nat.mul_add_div]

/-! ### bitwise -/

@[local simp]
private theorem eq_0_of_lt_one (x : Nat) : x < 1 ↔ x = 0 :=
  Iff.intro
    (fun p =>
      match x with
      | 0 => Eq.refl 0
      | _+1 => False.elim (not_lt_zero _ (Nat.lt_of_succ_lt_succ p)))
    (fun p => by simp [p])

private theorem eq_0_of_lt (x : Nat) : x < 2^ 0 ↔ x = 0 := eq_0_of_lt_one x

@[local simp]
private theorem zero_lt_pow (n : Nat) : 0 < 2^n := by
  induction n
  case zero => simp [eq_0_of_lt]
  case succ n hyp => simpa [Nat.pow_succ]

private theorem div_two_le_of_lt_two {m n : Nat} (p : m < 2 ^ succ n) : m / 2 < 2^n := by
  simp [div_lt_iff_lt_mul Nat.zero_lt_two]
  exact p

/-- This provides a bound on bitwise operations. -/
theorem bitwise_lt_two_pow (left : x < 2^n) (right : y < 2^n) : (Nat.bitwise f x y) < 2^n := by
  induction n generalizing x y with
  | zero =>
    simp only [eq_0_of_lt] at left right
    unfold bitwise
    simp [left, right]
  | succ n hyp =>
    unfold bitwise
    if x_zero : x = 0 then
      simp only [x_zero, if_pos]
      by_cases p : f false true = true <;> simp [p, right]
    else if y_zero : y = 0 then
      simp only [x_zero, y_zero, if_neg, if_pos]
      by_cases p : f true false = true <;> simp [p, left]
    else
      simp only [x_zero, y_zero, if_neg]
      have hyp1 := hyp (div_two_le_of_lt_two left) (div_two_le_of_lt_two right)
      by_cases p : f (decide (x % 2 = 1)) (decide (y % 2 = 1)) = true <;>
        simp [p, Nat.pow_succ, mul_succ, Nat.add_assoc]
      case pos =>
        apply lt_of_succ_le
        simp only [← Nat.succ_add]
        apply Nat.add_le_add <;> exact hyp1
      case neg =>
        apply Nat.add_lt_add <;> exact hyp1

/-! ### and -/

@[simp] theorem testBit'_and (x y i : Nat) : (x &&& y).testBit' i = (x.testBit' i && y.testBit' i) := by
  simp [HAnd.hAnd, AndOp.and, land, testBit'_bitwise ]

theorem and_lt_two_pow (x : Nat) {y n : Nat} (right : y < 2^n) : (x &&& y) < 2^n := by
  apply lt_pow_two_of_testBit'
  intro i i_ge_n
  have yf : testBit' y i = false := by
          apply Nat.testBit'_lt_two_pow
          apply Nat.lt_of_lt_of_le right
          exact pow_le_pow_of_le_right Nat.zero_lt_two i_ge_n
  simp [testBit'_and, yf]

@[simp] theorem and_pow_two_is_mod (x n : Nat) : x &&& (2^n-1) = x % 2^n := by
  apply eq_of_testBit'_eq
  intro i
  simp only [testBit'_and, testBit'_mod_two_pow]
  cases testBit' x i <;> simp

theorem and_pow_two_identity {x : Nat} (lt : x < 2^n) : x &&& 2^n-1 = x := by
  rw [and_pow_two_is_mod]
  apply Nat.mod_eq_of_lt lt

/-! ### lor -/

@[simp] theorem or_zero (x : Nat) : 0 ||| x = x := by
  simp only [HOr.hOr, OrOp.or, lor]
  unfold bitwise
  simp [@eq_comm _ 0]

@[simp] theorem zero_or (x : Nat) : x ||| 0 = x := by
  simp only [HOr.hOr, OrOp.or, lor]
  unfold bitwise
  simp [@eq_comm _ 0]

@[simp] theorem testBit'_or (x y i : Nat) : (x ||| y).testBit' i = (x.testBit' i || y.testBit' i) := by
  simp [HOr.hOr, OrOp.or, lor, testBit'_bitwise ]

theorem or_lt_two_pow {x y n : Nat} (left : x < 2^n) (right : y < 2^n) : x ||| y < 2^n :=
  bitwise_lt_two_pow left right

/-! ### xor -/

@[simp] theorem testBit'_xor (x y i : Nat) :
    (x ^^^ y).testBit' i = Bool.xor (x.testBit' i) (y.testBit' i) := by
  simp [HXor.hXor, Xor.xor, xor, testBit'_bitwise ]

theorem xor_lt_two_pow {x y n : Nat} (left : x < 2^n) (right : y < 2^n) : x ^^^ y < 2^n :=
  bitwise_lt_two_pow left right

/-! ### Arithmetic -/

theorem testBit'_mul_pow_two_add (a : Nat) {b i : Nat} (b_lt : b < 2^i) (j : Nat) :
    testBit' (2 ^ i * a + b) j =
      if j < i then
        testBit' b j
      else
        testBit' a (j - i) := by
  cases Nat.lt_or_ge j i with
  | inl j_lt =>
    simp only [j_lt]
    have i_def : i = j + succ (pred (i-j)) := by
      rw [succ_pred_eq_of_pos] <;> omega
    rw [i_def]
    simp only [testBit'_to_div_mod, Nat.pow_add, Nat.mul_assoc]
    simp only [Nat.mul_add_div (Nat.two_pow_pos _), Nat.mul_add_mod]
    simp [Nat.pow_succ, Nat.mul_comm _ 2, Nat.mul_assoc, Nat.mul_add_mod]
  | inr j_ge =>
    have j_def : j = i + (j-i) := (Nat.add_sub_cancel' j_ge).symm
    simp only [
        testBit'_to_div_mod,
        Nat.not_lt_of_le,
        j_ge,
        ite_false]
    simp [congrArg (2^·) j_def, Nat.pow_add,
          ←Nat.div_div_eq_div_mul,
          Nat.mul_add_div,
          Nat.div_eq_of_lt b_lt,
          Nat.two_pow_pos i]

theorem testBit'_mul_pow_two :
    testBit' (2 ^ i * a) j = (decide (j ≥ i) && testBit' a (j-i)) := by
  have gen := testBit'_mul_pow_two_add a (Nat.two_pow_pos i) j
  simp at gen
  rw [gen]
  cases Nat.lt_or_ge j i with
  | _ p => simp [p, Nat.not_le_of_lt, Nat.not_lt_of_le]

theorem mul_add_lt_is_or {b : Nat} (b_lt : b < 2^i) (a : Nat) : 2^i * a + b = 2^i * a ||| b := by
  apply eq_of_testBit'_eq
  intro j
  simp only [testBit'_mul_pow_two_add _ b_lt,
        testBit'_or, testBit'_mul_pow_two]
  if j_lt : j < i then
    simp [Nat.not_le_of_lt, j_lt]
  else
    have i_le : i ≤ j := Nat.le_of_not_lt j_lt
    have b_lt_j :=
            calc b < 2 ^ i := b_lt
                 _ ≤ 2 ^ j := Nat.pow_le_pow_of_le_right Nat.zero_lt_two i_le
    simp [i_le, j_lt, testBit'_lt_two_pow, b_lt_j]

/-! ### shiftLeft and shiftRight -/

@[simp] theorem testBit'_shiftLeft (x : Nat) : testBit' (x <<< i) j =
    (decide (j ≥ i) && testBit' x (j-i)) := by
  simp [shiftLeft_eq, Nat.mul_comm _ (2^_), testBit'_mul_pow_two]

@[simp] theorem testBit'_shiftRight (x : Nat) : testBit' (x >>> i) j = testBit' x (i+j) := by
  simp [testBit', ←shiftRight_add]
