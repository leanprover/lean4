/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/

prelude
import .lemmas init.meta.well_founded_tactics

universe u

namespace nat

  def shiftl : ℕ → ℕ → ℕ
  | m 0     := m
  | m (n+1) := 2 * shiftl m n

  def shiftr : ℕ → ℕ → ℕ
  | m 0     := m
  | m (n+1) := shiftr m n / 2

  def bodd (n : ℕ) : bool := n % 2 = 1

  def test_bit (m n : ℕ) : bool := bodd (shiftr m n)

  def bit (b : bool) : ℕ → ℕ := cond b bit1 bit0

  lemma bit0_val (n : nat) : bit0 n = 2 * n := (two_mul _).symm

  lemma bit1_val (n : nat) : bit1 n = 2 * n + 1 := congr_arg succ (bit0_val _)

  lemma bit_val (b n) : bit b n = 2 * n + cond b 1 0 :=
  by { cases b, apply bit0_val, apply bit1_val }

  lemma mod_two_of_bodd (n : nat) : n % 2 = cond (bodd n) 1 0 :=
  match by apply_instance : ∀ d, n % 2 = cond (@to_bool (n % 2 = 1) d) 1 0 with
  | is_true  h := h
  | is_false h := (mod_two_eq_zero_or_one _).resolve_right h
  end

  lemma bit_decomp (n : nat) : bit (bodd n) (shiftr n 1) = n :=
  (bit_val _ _).trans $ (add_comm _ _).trans $
  eq.trans (by rw mod_two_of_bodd; refl) (mod_add_div n 2)

  lemma bit_cases_on {C : nat → Sort u} (n) (h : ∀ b n, C (bit b n)) : C n :=
  by rw -bit_decomp n; apply h

  lemma bodd_bit (b n) : bodd (bit b n) = b :=
  begin
    rw bit_val, dsimp [bodd],
    rw [add_comm, add_mul_mod_self_left, mod_eq_of_lt];
    cases b; exact dec_trivial
  end

  lemma shiftr1_bit (b n) : shiftr (bit b n) 1 = n :=
  begin
    rw bit_val, dsimp [shiftr],
    rw [add_comm, add_mul_div_left, div_eq_of_lt, zero_add];
    cases b; exact dec_trivial
  end

  def shiftl_add (m n) : ∀ k, shiftl m (n + k) = shiftl (shiftl m n) k
  | 0     := rfl
  | (k+1) := congr_arg ((*) 2) (shiftl_add k)

  def shiftr_add (m n) : ∀ k, shiftr m (n + k) = shiftr (shiftr m n) k
  | 0     := rfl
  | (k+1) := congr_arg (/ 2) (shiftr_add k)

  def shiftl_eq_mul_pow (m) : ∀ n, shiftl m n = m * 2 ^ n
  | 0     := (mul_one _).symm
  | (k+1) := (congr_arg ((*) 2) (shiftl_eq_mul_pow k)).trans $ by simp [pow_succ]

  def one_shiftl (n) : shiftl 1 n = 2 ^ n :=
  (shiftl_eq_mul_pow _ _).trans (one_mul _)

  def zero_shiftl (n) : shiftl 0 n = 0 :=
  (shiftl_eq_mul_pow _ _).trans (zero_mul _)

  def shiftr_eq_div_pow (m) : ∀ n, shiftr m n = m / 2 ^ n
  | 0     := (nat.div_one _).symm
  | (k+1) := (congr_arg (/ 2) (shiftr_eq_div_pow k)).trans $
             by dsimp; rw [nat.div_div_eq_div_mul]; refl

  def zero_shiftr (n) : shiftr 0 n = 0 :=
  (shiftr_eq_div_pow _ _).trans (nat.zero_div _)

  def test_bit_zero (b n) : test_bit (bit b n) 0 = b := bodd_bit _ _

  def test_bit_succ (m b n) : test_bit (bit b n) (succ m) = test_bit n m :=
  have bodd (shiftr (shiftr (bit b n) 1) m) = bodd (shiftr n m), by rw shiftr1_bit,
  by rw [-shiftr_add, add_comm] at this; exact this

  def binary_rec {C : nat → Sort u} (f : ∀ b n, C n → C (bit b n)) (z : C 0) : Π n, C n
  | n := if n0 : n = 0 then by rw n0; exact z else let n' := shiftr n 1 in
    have n' < n, from (div_lt_iff_lt_mul _ _ dec_trivial).2 $
    by have := nat.mul_lt_mul_of_pos_left (dec_trivial : 1 < 2)
         (lt_of_le_of_ne (zero_le _) (ne.symm n0));
       rwa mul_one at this,
    by rw [-show bit (bodd n) n' = n, from bit_decomp n]; exact 
    f (bodd n) n' (binary_rec n')

  def size : ℕ → ℕ := binary_rec (λ_ _, succ) 0

  def bits : ℕ → list bool := binary_rec (λb _ IH, b :: IH) []

  def bitwise (f : bool → bool → bool) : ℕ → ℕ → ℕ :=
  binary_rec
    (λa m Ia, binary_rec
      (λb n _, bit (f a b) (Ia n))
      (cond (f tt ff) (bit a m) 0))
    (λn, cond (f ff tt) n 0)

  def lor   : ℕ → ℕ → ℕ := bitwise bor
  def land  : ℕ → ℕ → ℕ := bitwise band
  def ldiff : ℕ → ℕ → ℕ := bitwise (λ a b, a && bnot b)
  def lxor  : ℕ → ℕ → ℕ := bitwise bxor

  set_option type_context.unfold_lemmas true
  lemma binary_rec_eq {C : nat → Sort u} {f : ∀ b n, C n → C (bit b n)} {z}
    (h : f ff 0 z = z) (b n) :
    binary_rec f z (bit b n) = f b n (binary_rec f z n) :=
  begin
    rw [binary_rec.equations._eqn_1],
    cases (by apply_instance : decidable (bit b n = 0)) with b0 b0; dsimp [dite],
    { generalize (binary_rec._main._pack._proof_2 (bit b n)) e,
      rw [bodd_bit, shiftr1_bit], intro e, refl },
    { generalize (binary_rec._main._pack._proof_1 (bit b n) b0) e,
      have bf := bodd_bit b n, have n0 := shiftr1_bit b n,
      rw b0 at bf n0, rw [-show ff = b, from bf, -show 0 = n, from n0], intro e,
      exact h.symm },
  end

  lemma binary_rec_zero {C : nat → Sort u} (f : ∀ b n, C n → C (bit b n)) (z) :
    binary_rec f z 0 = z := by {rw [binary_rec.equations._eqn_1], refl}

  lemma bitwise_bit_aux {f : bool → bool → bool} (h : f ff ff = ff) :
    @binary_rec (λ_, ℕ)
      (λ b n _, bit (f ff b) (cond (f ff tt) n 0))
      (cond (f tt ff) (bit ff 0) 0) =
    λ (n : ℕ), cond (f ff tt) n 0 :=
  begin
    apply funext, intro n,
    apply bit_cases_on n, intros b n, rw [binary_rec_eq],
    { cases b; try {rw h}; ginduction f ff tt with fft; dsimp [cond]; refl },
    { rw [h, show cond (f ff tt) 0 0 = 0, by cases f ff tt; refl,
             show cond (f tt ff) (bit ff 0) 0 = 0, by cases f tt ff; refl]; refl }
  end

  lemma bitwise_zero_left (f : bool → bool → bool) (n) :
    bitwise f 0 n = cond (f ff tt) n 0 :=
  by unfold bitwise; rw [binary_rec_zero]

  lemma bitwise_zero_right (f : bool → bool → bool) (h : f ff ff = ff) (m) :
    bitwise f m 0 = cond (f tt ff) m 0 :=
  by unfold bitwise; apply bit_cases_on m; intros;
     rw [binary_rec_eq, binary_rec_zero]; exact bitwise_bit_aux h

  lemma bitwise_zero (f : bool → bool → bool) :
    bitwise f 0 0 = 0 :=
  by rw bitwise_zero_left; cases f ff tt; refl

  lemma bitwise_bit {f : bool → bool → bool} (h : f ff ff = ff) (a m b n) :
    bitwise f (bit a m) (bit b n) = bit (f a b) (bitwise f m n) :=
  begin
    unfold bitwise,
    rw [binary_rec_eq, binary_rec_eq],
    { ginduction f tt ff with ftf; dsimp [cond],
      rw [show f a ff = ff, by cases a; assumption],
      apply @congr_arg _ _ _ 0 (bit ff), tactic.swap,
      rw [show f a ff = a, by cases a; assumption],
      apply congr_arg (bit a),
      all_goals {
        apply bit_cases_on m, intros a m,
        rw [binary_rec_eq, binary_rec_zero],
        rw [-bitwise_bit_aux h, ftf], refl } },
    { exact bitwise_bit_aux h }
  end

  lemma lor_bit : ∀ (a m b n),
    lor (bit a m) (bit b n) = bit (a || b) (lor m n) := bitwise_bit rfl
  lemma land_bit : ∀ (a m b n),
    land (bit a m) (bit b n) = bit (a && b) (land m n) := bitwise_bit rfl
  lemma ldiff_bit : ∀ (a m b n),
    ldiff (bit a m) (bit b n) = bit (a && bnot b) (ldiff m n) := bitwise_bit rfl
  lemma lxor_bit : ∀ (a m b n),
    lxor (bit a m) (bit b n) = bit (bxor a b) (lxor m n) := bitwise_bit rfl

  def test_bit_bitwise {f : bool → bool → bool} (h : f ff ff = ff) (m n k) :
    test_bit (bitwise f m n) k = f (test_bit m k) (test_bit n k) :=
  begin
    revert m n; induction k with k IH; intros m n;
    apply bit_cases_on m; intros a m';
    apply bit_cases_on n; intros b n';
    rw bitwise_bit h,
    { simp [test_bit_zero] },
    { simp [test_bit_succ, IH] }
  end

  lemma test_bit_lor : ∀ (m n k),
    test_bit (lor m n) k = test_bit m k || test_bit n k := test_bit_bitwise rfl
  lemma test_bit_land : ∀ (m n k),
    test_bit (land m n) k = test_bit m k && test_bit n k := test_bit_bitwise rfl
  lemma test_bit_ldiff : ∀ (m n k),
    test_bit (ldiff m n) k = test_bit m k && bnot (test_bit n k) := test_bit_bitwise rfl
  lemma test_bit_lxor : ∀ (m n k),
    test_bit (lxor m n) k = bxor (test_bit m k) (test_bit n k) := test_bit_bitwise rfl

end nat
