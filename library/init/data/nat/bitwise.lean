/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/

prelude
import init.data.nat.lemmas init.meta.well_founded_tactics

universe u

namespace nat

  def bodd_div2 : ℕ → bool × ℕ
  | 0        := (ff, 0)
  | (succ n) :=
    match bodd_div2 n with
    | (ff, m) := (tt, m)
    | (tt, m) := (ff, succ m)
    end

  def div2 (n : ℕ) : ℕ := (bodd_div2 n).2

  def bodd (n : ℕ) : bool := (bodd_div2 n).1

  @[simp] lemma bodd_zero : bodd 0 = ff := rfl
  @[simp] lemma bodd_one : bodd 1 = tt := rfl
  @[simp] lemma bodd_two : bodd 2 = ff := rfl

  @[simp] lemma bodd_succ (n : ℕ) : bodd (succ n) = bnot (bodd n) :=
  by unfold bodd bodd_div2; cases bodd_div2 n; cases fst; refl

  @[simp] lemma bodd_add (m n : ℕ) : bodd (m + n) = bxor (bodd m) (bodd n) :=
  begin
    induction n with n IH,
    { simp, cases bodd m; refl },
    { simp [IH], cases bodd m; cases bodd n; refl }
  end

  @[simp] lemma bodd_mul (m n : ℕ) : bodd (m * n) = bodd m && bodd n :=
  begin
    induction n with n IH,
    { simp, cases bodd m; refl },
    { simp [mul_succ, IH], cases bodd m; cases bodd n; refl }
  end

  lemma mod_two_of_bodd (n : ℕ) : n % 2 = cond (bodd n) 1 0 :=
  begin
    have := congr_arg bodd (mod_add_div n 2),
    simp [bnot] at this,
    rw [show ∀ b, ff && b = ff, by intros; cases b; refl,
        show ∀ b, bxor b ff = b, by intros; cases b; refl] at this,
    rw [← this],
    cases mod_two_eq_zero_or_one n; rw a; refl
  end

  @[simp] lemma div2_zero : div2 0 = 0 := rfl
  @[simp] lemma div2_one : div2 1 = 0 := rfl
  @[simp] lemma div2_two : div2 2 = 1 := rfl

  @[simp] lemma div2_succ (n : ℕ) : div2 (succ n) = cond (bodd n) (succ (div2 n)) (div2 n) :=
  by unfold bodd div2 bodd_div2; cases bodd_div2 n; cases fst; refl

  theorem bodd_add_div2 : ∀ n, cond (bodd n) 1 0 + 2 * div2 n = n
  | 0        := rfl
  | (succ n) := begin
    simp,
    refine eq.trans _ (congr_arg succ (bodd_add_div2 n)),
    cases bodd n; simp [cond, bnot],
    { rw add_comm; refl },
    { rw [succ_mul, add_comm 1] }
  end

  theorem div2_val (n) : div2 n = n / 2 :=
  by refine eq_of_mul_eq_mul_left dec_trivial
      (nat.add_left_cancel (eq.trans _ (mod_add_div n 2).symm));
     rw [mod_two_of_bodd, bodd_add_div2]

  def bit (b : bool) : ℕ → ℕ := cond b bit1 bit0

  lemma bit0_val (n : nat) : bit0 n = 2 * n := (two_mul _).symm

  lemma bit1_val (n : nat) : bit1 n = 2 * n + 1 := congr_arg succ (bit0_val _)

  lemma bit_val (b n) : bit b n = 2 * n + cond b 1 0 :=
  by { cases b, apply bit0_val, apply bit1_val }

  lemma bit_decomp (n : nat) : bit (bodd n) (div2 n) = n :=
  (bit_val _ _).trans $ (add_comm _ _).trans $ bodd_add_div2 _

  def bit_cases_on {C : nat → Sort u} (n) (h : ∀ b n, C (bit b n)) : C n :=
  by rw [← bit_decomp n]; apply h

  @[simp] lemma bit_zero : bit ff 0 = 0 := rfl

  def shiftl' (b : bool) (m : ℕ) : ℕ → ℕ
  | 0     := m
  | (n+1) := bit b (shiftl' n)

  def shiftl : ℕ → ℕ → ℕ := shiftl' ff

  def shiftr : ℕ → ℕ → ℕ
  | m 0     := m
  | m (n+1) := div2 (shiftr m n)

  def test_bit (m n : ℕ) : bool := bodd (shiftr m n)

  def binary_rec {C : nat → Sort u} (z : C 0) (f : ∀ b n, C n → C (bit b n)) : Π n, C n
  | n := if n0 : n = 0 then by rw n0; exact z else let n' := div2 n in
    have n' < n, begin
      change div2 n < n, rw div2_val,
      apply (div_lt_iff_lt_mul _ _ (succ_pos 1)).2,
      have := nat.mul_lt_mul_of_pos_left (lt_succ_self 1)
        (lt_of_le_of_ne (zero_le _) (ne.symm n0)),
      rwa mul_one at this
    end,
    by rw [← show bit (bodd n) n' = n, from bit_decomp n]; exact
    f (bodd n) n' (binary_rec n')

  def size : ℕ → ℕ := binary_rec 0 (λ_ _, succ)

  def bits : ℕ → list bool := binary_rec [] (λb _ IH, b :: IH)

  def bitwise (f : bool → bool → bool) : ℕ → ℕ → ℕ :=
  binary_rec
    (λn, cond (f ff tt) n 0)
    (λa m Ia, binary_rec
      (cond (f tt ff) (bit a m) 0)
      (λb n _, bit (f a b) (Ia n)))

  def lor   : ℕ → ℕ → ℕ := bitwise bor
  def land  : ℕ → ℕ → ℕ := bitwise band
  def ldiff : ℕ → ℕ → ℕ := bitwise (λ a b, a && bnot b)
  def lxor  : ℕ → ℕ → ℕ := bitwise bxor

  @[simp] lemma binary_rec_zero {C : nat → Sort u} (z : C 0) (f : ∀ b n, C n → C (bit b n)) :
    binary_rec z f 0 = z :=
  by {rw [binary_rec], refl}

end nat
