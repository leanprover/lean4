/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

A proof that the square root of an integer is irrational, unless the integer is a perfect square.
-/
import data.rat
open nat eq.ops

/- First, a textbook proof that sqrt 2 is irrational. -/

theorem sqrt_two_irrational_aux {a b : ℕ} (co : coprime a b) : a * a ≠ 2 * (b * b) :=
assume H : a * a = 2 * (b * b),
have even (a * a), from even_of_exists (exists.intro _ H),
have even a, from even_of_even_mul_self this,
obtain c (aeq : a = 2 * c), from exists_of_even this,
have 2 * (2 * (c * c)) = 2 * (b * b), by rewrite [-H, aeq, mul.assoc, mul.left_comm c],
have 2 * (c * c) = b * b, from eq_of_mul_eq_mul_left dec_trivial this,
have even (b * b), from even_of_exists (exists.intro _ (eq.symm this)),
have even b, from even_of_even_mul_self this,
have 2 ∣ gcd a b, from dvd_gcd (dvd_of_even `even a`) (dvd_of_even `even b`),
have 2 ∣ 1, from co ▸ this,
absurd `2 ∣ 1` dec_trivial

/- Let's state this in terms of rational numbers. The problem is that we now have to mediate between
   rat, int, and nat. -/

section
  open rat int

  theorem sqrt_two_irrational (q : ℚ): q^2 ≠ 2 :=
  suppose q^2 = 2,
  let a := num q, b := denom q in
  have b ≠ 0, from ne_of_gt (denom_pos q),
  assert bnz : b ≠ (0 : ℚ), from assume H, `b ≠ 0` (of_int.inj H),
  have b * b ≠ (0 : ℚ), from rat.mul_ne_zero bnz bnz,
  have (a * a) / (b * b) = 2,
    by rewrite [*of_int_mul, -div_mul_div bnz bnz, -eq_num_div_denom, -this, rat.pow_two],
  have a * a = 2 * (b * b), from eq.symm (mul_eq_of_eq_div `b * b ≠ (0 : ℚ)` this⁻¹),
  assert a * a = 2 * (b * b), from of_int.inj this,    -- now in the integers
  let a' := nat_abs a, b' := nat_abs b in
  have H : a' * a' = 2 * (b' * b'),
    begin
      apply of_nat.inj,
      rewrite [-+nat_abs_mul, int.of_nat_mul, +of_nat_nat_abs, +int.abs_mul_self],
      exact this,
    end,
  have coprime a b, from !coprime_num_denom,
  have nat.coprime a' b', from of_nat.inj this,
  show false, from sqrt_two_irrational_aux this H
end
