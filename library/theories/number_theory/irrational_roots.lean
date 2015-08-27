/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

A proof that if n > 1 and a > 0, then the nth root of a is irrational, unless a is a perfect nth power.
-/
import data.rat .prime_factorization
open eq.ops

/- First, a textbook proof that sqrt 2 is irrational. -/

section
  open nat

  theorem sqrt_two_irrational {a b : ℕ} (co : coprime a b) : a^2 ≠ 2 * b^2 :=
  assume H : a^2 = 2 * b^2,
  have even (a^2), from even_of_exists (exists.intro _ H),
  have even a, from even_of_even_pow this,
  obtain c (aeq : a = 2 * c), from exists_of_even this,
  have 2 * (2 * c^2) = 2 * b^2, by rewrite [-H, aeq, *pow_two, mul.assoc, mul.left_comm c],
  have 2 * c^2 = b^2, from eq_of_mul_eq_mul_left dec_trivial this,
  have even (b^2), from even_of_exists (exists.intro _ (eq.symm this)),
  have even b, from even_of_even_pow this,
  have 2 ∣ gcd a b, from dvd_gcd (dvd_of_even `even a`) (dvd_of_even `even b`),
  have 2 ∣ 1, from co ▸ this,
  absurd `2 ∣ 1` dec_trivial
end

/-
  Replacing 2 by an arbitrary prime and the power 2 by any n ≥ 1 yields the stronger result
  that the nth root of an integer is irrational, unless the integer is already a perfect nth
  power.
-/

section
  open nat decidable

  theorem root_irrational {a b c n : ℕ} (npos : n > 0) (apos : a > 0) (co : coprime a b)
      (H : a^n = c * b^n) :
    b = 1 :=
  have bpos : b > 0, from pos_of_ne_zero
    (suppose b = 0,
      have a^n = 0, by rewrite [H, this, zero_pow npos],
      assert a = 0, from eq_zero_of_pow_eq_zero this,
      show false, from ne_of_lt `0 < a` this⁻¹),
  have H₁ : ∀ p, prime p → ¬ p ∣ b, from
    take p, suppose prime p, suppose p ∣ b,
    assert p ∣ b^n, from dvd_pow_of_dvd_of_pos `p ∣ b` `n > 0`,
    have p ∣ a^n, by rewrite H; apply dvd_mul_of_dvd_right this,
    have p ∣ a, from dvd_of_prime_of_dvd_pow `prime p` this,
    have ¬ coprime a b, from not_coprime_of_dvd_of_dvd (gt_one_of_prime `prime p`) `p ∣ a` `p ∣ b`,
    show false, from this `coprime a b`,
  have b < 2, from by_contradiction
    (suppose ¬ b < 2,
      have b ≥ 2, from le_of_not_gt this,
      obtain p [primep pdvdb], from exists_prime_and_dvd this,
      show false, from H₁ p primep pdvdb),
  show b = 1, from (le.antisymm (le_of_lt_succ `b < 2`) (succ_le_of_lt `b > 0`))
end

/-
  Here we state this in terms of the rationals, ℚ. The main difficulty is casting between ℕ, ℤ,
  and ℚ.
-/

section
  open rat int nat decidable

  theorem denom_eq_one_of_pow_eq {q : ℚ} {n : ℕ} {c : ℤ} (npos : n > 0) (H : q^n = c) :
    denom q = 1 :=
  let a := num q, b := denom q in
  have b ≠ 0, from ne_of_gt (denom_pos q),
  have bnz : b ≠ (0 : ℚ), from assume H, `b ≠ 0` (of_int.inj H),
  have bnnz : (#rat b^n ≠ 0), from assume bneqz, bnz (eq_zero_of_pow_eq_zero bneqz),
  have a^n / b^n = c, using bnz, by rewrite [*of_int_pow, -div_pow, -eq_num_div_denom, -H],
  have a^n = c * b^n, from eq.symm (!mul_eq_of_eq_div bnnz this⁻¹),
  have a^n = c * b^n,  -- int version
    using this, by rewrite [-of_int_pow at this, -of_int_mul at this]; exact of_int.inj this,
  have (abs a)^n = abs c * (abs b)^n,
    using this, by rewrite [-int.abs_pow, this, int.abs_mul, int.abs_pow],
  have H₁ : (nat_abs a)^n = nat_abs c * (nat_abs b)^n,
    using this,
      by apply of_nat.inj; rewrite [int.of_nat_mul, +of_nat_pow, +of_nat_nat_abs]; assumption,
  have H₂ : nat.coprime (nat_abs a) (nat_abs b), from of_nat.inj !coprime_num_denom,
  have nat_abs b = 1, from
    by_cases
      (suppose q = 0, by rewrite this)
      (suppose q ≠ 0,
        have a ≠ 0, from suppose a = 0, `q ≠ 0` (by rewrite [eq_num_div_denom, `a = 0`, zero_div]),
        have nat_abs a ≠ 0, from suppose nat_abs a = 0, `a ≠ 0` (eq_zero_of_nat_abs_eq_zero this),
        show nat_abs b = 1, from (root_irrational npos (pos_of_ne_zero this) H₂ H₁)),
  show b = 1, using this, by rewrite [-of_nat_nat_abs_of_nonneg (le_of_lt !denom_pos), this]

  theorem eq_num_pow_of_pow_eq {q : ℚ} {n : ℕ} {c : ℤ} (npos : n > 0) (H : q^n = c) :
    c = (num q)^n :=
  have denom q = 1, from denom_eq_one_of_pow_eq npos H,
  have of_int c = (num q)^n, using this,
    by rewrite [-H, eq_num_div_denom q at {1}, this, div_one, of_int_pow],
  show c = (num q)^n , from of_int.inj this
end

/- As a corollary, for n > 1, the nth root of a prime is irrational. -/

section
  open nat

  theorem not_eq_pow_of_prime {p n : ℕ} (a : ℕ) (ngt1 : n > 1) (primep : prime p) : p ≠ a^n :=
  assume peq : p = a^n,
  have npos : n > 0, from lt.trans dec_trivial ngt1,
  have pnez : p ≠ 0, from
    (suppose p = 0,
      show false,
        by let H := (pos_of_prime primep); rewrite this at H; exfalso; exact !lt.irrefl H),
  have agtz : a > 0, from pos_of_ne_zero
    (suppose a = 0,
      show false, using npos pnez, by revert peq; rewrite [this, zero_pow npos]; exact pnez),
  have n * mult p a = 1, from calc
    n * mult p a = mult p (a^n) : using agtz, by rewrite [mult_pow n agtz primep]
             ... = mult p p     : peq
             ... = 1            : mult_self (gt_one_of_prime primep),
  have n ∣ 1, from dvd_of_mul_right_eq this,
  have n = 1, from eq_one_of_dvd_one this,
  show false, using this, by rewrite this at ngt1; exact !lt.irrefl ngt1

  open int rat

  theorem root_prime_irrational {p n : ℕ} {q : ℚ} (qnonneg : q ≥ 0) (ngt1 : n > 1)
      (primep : prime p) :
    q^n ≠ p :=
  have numq : num q ≥ 0, from num_nonneg_of_nonneg qnonneg,
  have npos : n > 0, from lt.trans dec_trivial ngt1,
  suppose q^n = p,
  have p = (num q)^n, from eq_num_pow_of_pow_eq npos this,
  have p = (nat_abs (num q))^n, using this numq,
    by apply of_nat.inj; rewrite [this, of_nat_pow, of_nat_nat_abs_of_nonneg numq],
  show false, from not_eq_pow_of_prime _ ngt1 primep this
end

/-
  Thaetetus, who lives in the fourth century BC, is said to have proved the irrationality of square
  roots up to seventeen. In Chapter 4 of /Why Prove it Again/, John Dawson notes that Thaetetus may
  have used an approach similar to the one below. (See data/nat/gcd.lean for the key theorem,
  "div_gcd_eq_div_gcd".)
-/

section
  open int

  example {a b c : ℤ} (co : coprime a b) (apos : a > 0) (bpos : b > 0)
      (H : a * a = c * (b * b)) :
    b = 1 :=
  assert H₁ : gcd (c * b) a = gcd c a, from gcd_mul_right_cancel_of_coprime _ (coprime_swap co),
  have a * a = c * b * b, by rewrite -mul.assoc at H; apply H,
  have a div (gcd a b) = c * b div gcd (c * b) a, from div_gcd_eq_div_gcd this bpos apos,
  have a = c * b div gcd c a,
    using this, by revert this; rewrite [↑coprime at co, co, div_one, H₁]; intros; assumption,
  have a = b * (c div gcd c a),
    using this,
      by revert this; rewrite [mul.comm, !mul_div_assoc !gcd_dvd_left]; intros; assumption,
  have b ∣ a, from dvd_of_mul_right_eq this⁻¹,
  have b ∣ gcd a b, from dvd_gcd this !dvd.refl,
  have b ∣ 1, using this, by rewrite [↑coprime at co, co at this]; apply this,
  show b = 1, from eq_one_of_dvd_one (le_of_lt bpos) this
end
