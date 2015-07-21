/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

Definitions and properties of gcd, lcm, and coprime.
-/
import .div data.nat.gcd
open eq.ops

namespace int

/- gcd -/

definition gcd (a b : ℤ) : ℤ := of_nat (nat.gcd (nat_abs a) (nat_abs b))

theorem gcd_nonneg (a b : ℤ) : gcd a b ≥ 0 :=
of_nat_nonneg (nat.gcd (nat_abs a) (nat_abs b))

theorem gcd.comm (a b : ℤ) : gcd a b = gcd b a :=
by rewrite [↑gcd, nat.gcd.comm]

theorem gcd_zero_right (a : ℤ) : gcd a 0 = abs a :=
by krewrite [↑gcd, nat.gcd_zero_right, of_nat_nat_abs]

theorem gcd_zero_left (a : ℤ) : gcd 0 a = abs a :=
by rewrite [gcd.comm, gcd_zero_right]

theorem gcd_one_right (a : ℤ) : gcd a 1 = 1 :=
by krewrite [↑gcd, nat.gcd_one_right]

theorem gcd_one_left (a : ℤ) : gcd 1 a = 1 :=
by rewrite [gcd.comm, gcd_one_right]

theorem gcd_abs_left (a b : ℤ) : gcd (abs a) b = gcd a b :=
by rewrite [↑gcd, *nat_abs_abs]

theorem gcd_abs_right (a b : ℤ) : gcd (abs a) b = gcd a b :=
by rewrite [↑gcd, *nat_abs_abs]

theorem gcd_abs_abs (a b : ℤ) : gcd (abs a) (abs b) = gcd a b :=
by rewrite [↑gcd, *nat_abs_abs]

theorem gcd_of_ne_zero (a : ℤ) {b : ℤ} (H : b ≠ 0) : gcd a b = gcd b (abs a mod abs b) :=
have nat_abs b ≠ nat.zero,        from assume H', H (nat_abs_eq_zero H'),
have (#nat nat_abs b > nat.zero), from nat.pos_of_ne_zero this,
assert nat.gcd (nat_abs a) (nat_abs b) = (#nat nat.gcd (nat_abs b) (nat_abs a mod nat_abs b)),
  from @nat.gcd_of_pos (nat_abs a) (nat_abs b) this,
calc
 gcd a b = nat.gcd (nat_abs b) (#nat nat_abs a mod nat_abs b) : by rewrite [↑gcd, this]
     ... = gcd (abs b) (abs a mod abs b)                      :
               by rewrite [↑gcd, -*of_nat_nat_abs, of_nat_mod]
     ... = gcd b (abs a mod abs b)                            : by rewrite [↑gcd, *nat_abs_abs]

theorem gcd_of_pos (a : ℤ) {b : ℤ} (H : b > 0) : gcd a b = gcd b (abs a mod b) :=
by rewrite [!gcd_of_ne_zero (ne_of_gt H), abs_of_pos H]

theorem gcd_of_nonneg_of_pos {a b : ℤ} (H1 : a ≥ 0) (H2 : b > 0) : gcd a b = gcd b (a mod b) :=
by rewrite [!gcd_of_pos H2, abs_of_nonneg H1]

theorem gcd_self (a : ℤ) : gcd a a = abs a :=
by rewrite [↑gcd, nat.gcd_self, of_nat_nat_abs]

theorem gcd_dvd_left (a b : ℤ) : gcd a b ∣ a :=
have gcd a b ∣ abs a,
  by rewrite [↑gcd, -of_nat_nat_abs, of_nat_dvd_of_nat]; apply nat.gcd_dvd_left,
iff.mp !dvd_abs_iff this

theorem gcd_dvd_right (a b : ℤ) : gcd a b ∣ b :=
by rewrite gcd.comm; apply gcd_dvd_left

theorem dvd_gcd {a b c : ℤ} : a ∣ b → a ∣ c → a ∣ gcd b c :=
begin
  rewrite [↑gcd, -*(abs_dvd_iff a), -(dvd_abs_iff _ b), -(dvd_abs_iff _ c), -*of_nat_nat_abs],
  rewrite [*of_nat_dvd_of_nat] ,
  apply nat.dvd_gcd
end

theorem gcd.assoc (a b c : ℤ) : gcd (gcd a b) c = gcd a (gcd b c) :=
dvd.antisymm !gcd_nonneg !gcd_nonneg
  (dvd_gcd
    (dvd.trans !gcd_dvd_left !gcd_dvd_left)
    (dvd_gcd (dvd.trans !gcd_dvd_left !gcd_dvd_right) !gcd_dvd_right))
  (dvd_gcd
    (dvd_gcd !gcd_dvd_left (dvd.trans !gcd_dvd_right !gcd_dvd_left))
    (dvd.trans !gcd_dvd_right !gcd_dvd_right))

theorem gcd_mul_left (a b c : ℤ) : gcd (a * b) (a * c) = abs a * gcd b c :=
by rewrite [↑gcd, *nat_abs_mul, nat.gcd_mul_left, of_nat_mul, of_nat_nat_abs]

theorem gcd_mul_right (a b c : ℤ) : gcd (a * b) (c * b) = gcd a c * abs b :=
by rewrite [mul.comm a, mul.comm c, mul.comm (gcd a c), gcd_mul_left]

theorem gcd_pos_of_ne_zero_left {a : ℤ} (b : ℤ) (H : a ≠ 0) : gcd a b > 0 :=
have gcd a b ≠ 0, from
  suppose gcd a b = 0,
  have 0 ∣ a,    from this ▸ gcd_dvd_left a b,
  show false,    from H (eq_zero_of_zero_dvd this),
lt_of_le_of_ne (gcd_nonneg a b) (ne.symm this)

theorem gcd_pos_of_ne_zero_right (a : ℤ) {b : ℤ} (H : b ≠ 0) : gcd a b > 0 :=
by rewrite gcd.comm; apply !gcd_pos_of_ne_zero_left H

theorem eq_zero_of_gcd_eq_zero_left {a b : ℤ} (H : gcd a b = 0) : a = 0 :=
decidable.by_contradiction
  (suppose a ≠ 0,
    have gcd a b > 0, from !gcd_pos_of_ne_zero_left this,
    ne_of_lt this H⁻¹)

theorem eq_zero_of_gcd_eq_zero_right {a b : ℤ} (H : gcd a b = 0) : b = 0 :=
by rewrite gcd.comm at H; apply !eq_zero_of_gcd_eq_zero_left H

theorem gcd_div {a b c : ℤ} (H1 : c ∣ a) (H2 : c ∣ b) :
  gcd (a div c) (b div c) = gcd a b div (abs c) :=
decidable.by_cases
  (suppose c = 0,
    calc
      gcd (a div c) (b div c) = gcd 0 0             : by subst c; rewrite *div_zero
                          ... = 0                   : gcd_zero_left
                          ... = gcd a b div 0       : div_zero
                          ... = gcd a b div (abs c) : by subst c)
  (suppose c ≠ 0,
    have abs c ≠ 0, from assume H', this (eq_zero_of_abs_eq_zero H'),
    eq.symm (div_eq_of_eq_mul_left this
      (eq.symm (calc
        gcd (a div c) (b div c) * abs c = gcd (a div c * c) (b div c * c) : gcd_mul_right
                                ... = gcd a (b div c * c)                 : div_mul_cancel H1
                                ... = gcd a b                             : div_mul_cancel H2))))

theorem gcd_dvd_gcd_mul_left (a b c : ℤ) : gcd a b ∣ gcd (c * a) b :=
dvd_gcd (dvd.trans !gcd_dvd_left !dvd_mul_left) !gcd_dvd_right

theorem gcd_dvd_gcd_mul_right (a b c : ℤ) : gcd a b ∣ gcd (a * c) b :=
!mul.comm ▸ !gcd_dvd_gcd_mul_left

theorem div_gcd_eq_div_gcd_of_nonneg {a₁ b₁ a₂ b₂ : ℤ} (H : a₁ * b₂ = a₂ * b₁)
    (H1 : b₁ ≠ 0) (H2 : b₂ ≠ 0) (H3 : a₁ ≥ 0) (H4 : a₂ ≥ 0) :
  a₁ div (gcd a₁ b₁) = a₂ div (gcd a₂ b₂) :=
begin
  apply div_eq_div_of_dvd_of_dvd,
  repeat (apply gcd_dvd_left),
  intro H', apply H1, apply eq_zero_of_gcd_eq_zero_right H',
  intro H', apply H2, apply eq_zero_of_gcd_eq_zero_right H',
  rewrite [-abs_of_nonneg H3 at {1}, -abs_of_nonneg H4 at {2}],
  rewrite [-gcd_mul_left, -gcd_mul_right, H, mul.comm b₁]
end

theorem div_gcd_eq_div_gcd {a₁ b₁ a₂ b₂ : ℤ} (H : a₁ * b₂ = a₂ * b₁) (H1 : b₁ > 0) (H2 : b₂ > 0) :
  a₁ div (gcd a₁ b₁) = a₂ div (gcd a₂ b₂) :=
or.elim (le_or_gt 0 a₁)
  (assume H3 : a₁ ≥ 0,
    have H4 : a₂ * b₁ ≥ 0, by rewrite -H; apply mul_nonneg H3 (le_of_lt H2),
    have H5 : a₂ ≥ 0, from nonneg_of_mul_nonneg_right H4 H1,
    div_gcd_eq_div_gcd_of_nonneg H (ne_of_gt H1) (ne_of_gt H2) H3 H5)
  (assume H3 : a₁ < 0,
    have H4 : a₂ * b₁ < 0, by rewrite -H; apply mul_neg_of_neg_of_pos H3 H2,
    assert H5 : a₂ < 0, from neg_of_mul_neg_right H4 (le_of_lt H1),
    assert H6 : abs a₁ div (gcd (abs a₁) (abs b₁)) = abs a₂ div (gcd (abs a₂) (abs b₂)),
      begin
        apply div_gcd_eq_div_gcd_of_nonneg,
        rewrite [abs_of_pos H1, abs_of_pos H2, abs_of_neg H3, abs_of_neg H5],
        rewrite [-*neg_mul_eq_neg_mul, H],
        apply ne_of_gt (abs_pos_of_pos H1),
        apply ne_of_gt (abs_pos_of_pos H2),
        repeat (apply abs_nonneg)
      end,
    have H7 : -a₁ div (gcd a₁ b₁) = -a₂ div (gcd a₂ b₂),
      begin
        rewrite [-abs_of_neg H3, -abs_of_neg H5, -gcd_abs_abs a₁],
        rewrite [-gcd_abs_abs a₂ b₂],
        exact H6
      end,
    calc
      a₁ div (gcd a₁ b₁) = -(-a₁ div (gcd a₁ b₁)) :
                             by rewrite [neg_div_of_dvd !gcd_dvd_left, neg_neg]
                     ... = -(-a₂ div (gcd a₂ b₂)) : H7
                     ... = a₂ div (gcd a₂ b₂) :
                             by rewrite [neg_div_of_dvd !gcd_dvd_left, neg_neg])

/- lcm -/

definition lcm (a b : ℤ) : ℤ := of_nat (nat.lcm (nat_abs a) (nat_abs b))

theorem lcm_nonneg (a b : ℤ) : lcm a b ≥ 0 :=
of_nat_nonneg (nat.lcm (nat_abs a) (nat_abs b))

theorem lcm.comm (a b : ℤ) : lcm a b = lcm b a :=
by rewrite [↑lcm, nat.lcm.comm]

theorem lcm_zero_left (a : ℤ) : lcm 0 a = 0 :=
by krewrite [↑lcm, nat.lcm_zero_left]

theorem lcm_zero_right (a : ℤ) : lcm a 0 = 0 :=
!lcm.comm ▸ !lcm_zero_left

theorem lcm_one_left (a : ℤ) : lcm 1 a = abs a :=
by krewrite [↑lcm, nat.lcm_one_left, of_nat_nat_abs]

theorem lcm_one_right (a : ℤ) : lcm a 1 = abs a :=
!lcm.comm ▸ !lcm_one_left

theorem lcm_abs_left (a b : ℤ) : lcm (abs a) b = lcm a b :=
by rewrite [↑lcm, *nat_abs_abs]

theorem lcm_abs_right (a b : ℤ) : lcm (abs a) b = lcm a b :=
by rewrite [↑lcm, *nat_abs_abs]

theorem lcm_abs_abs (a b : ℤ) : lcm (abs a) (abs b) = lcm a b :=
by rewrite [↑lcm, *nat_abs_abs]

theorem lcm_self (a : ℤ) : lcm a a = abs a :=
by krewrite [↑lcm, nat.lcm_self, of_nat_nat_abs]

theorem dvd_lcm_left (a b : ℤ) : a ∣ lcm a b :=
by rewrite [↑lcm, -abs_dvd_iff, -of_nat_nat_abs, of_nat_dvd_of_nat]; apply nat.dvd_lcm_left

theorem dvd_lcm_right (a b : ℤ) : b ∣ lcm a b :=
!lcm.comm ▸ !dvd_lcm_left

theorem gcd_mul_lcm (a b : ℤ) : gcd a b * lcm a b = abs (a * b) :=
begin
  rewrite [↑gcd, ↑lcm, -of_nat_nat_abs, -of_nat_mul, of_nat_eq_of_nat, nat_abs_mul],
  apply nat.gcd_mul_lcm
end

theorem lcm_dvd {a b c : ℤ} : a ∣ c → b ∣ c → lcm a b ∣ c :=
begin
  rewrite [↑lcm, -(abs_dvd_iff a), -(abs_dvd_iff b), -*(dvd_abs_iff _ c), -*of_nat_nat_abs],
  rewrite [*of_nat_dvd_of_nat] ,
  apply nat.lcm_dvd
end

theorem lcm_assoc (a b c : ℤ) : lcm (lcm a b) c = lcm a (lcm b c) :=
dvd.antisymm !lcm_nonneg !lcm_nonneg
  (lcm_dvd
    (lcm_dvd !dvd_lcm_left (dvd.trans !dvd_lcm_left !dvd_lcm_right))
    (dvd.trans !dvd_lcm_right !dvd_lcm_right))
  (lcm_dvd
    (dvd.trans !dvd_lcm_left !dvd_lcm_left)
    (lcm_dvd (dvd.trans !dvd_lcm_right !dvd_lcm_left) !dvd_lcm_right))

/- coprime -/

abbreviation coprime (a b : ℤ) : Prop := gcd a b = 1

theorem coprime_swap {a b : ℤ} (H : coprime b a) : coprime a b :=
!gcd.comm ▸ H

theorem dvd_of_coprime_of_dvd_mul_right {a b c : ℤ} (H1 : coprime c b) (H2 : c ∣ a * b) : c ∣ a :=
assert H3 : gcd (a * c) (a * b) = abs a, from
  calc
    gcd (a * c) (a * b) = abs a * gcd c b : gcd_mul_left
                    ... = abs a * 1       : H1
                    ... = abs a           : mul_one,
assert H4 : (c ∣ gcd (a * c) (a * b)), from dvd_gcd !dvd_mul_left H2,
by rewrite [-dvd_abs_iff, -H3]; apply H4

theorem dvd_of_coprime_of_dvd_mul_left {a b c : ℤ} (H1 : coprime c a) (H2 : c ∣ a * b) : c ∣ b :=
dvd_of_coprime_of_dvd_mul_right H1 (!mul.comm ▸ H2)

theorem gcd_mul_left_cancel_of_coprime {c : ℤ} (a : ℤ) {b : ℤ} (H : coprime c b) :
   gcd (c * a) b = gcd a b :=
begin
  revert H, rewrite [↑coprime, ↑gcd, *of_nat_eq_of_nat, nat_abs_mul],
  apply nat.gcd_mul_left_cancel_of_coprime
end

theorem gcd_mul_right_cancel_of_coprime (a : ℤ) {c b : ℤ} (H : coprime c b) :
   gcd (a * c) b = gcd a b :=
!mul.comm ▸ !gcd_mul_left_cancel_of_coprime H

theorem gcd_mul_left_cancel_of_coprime_right {c a : ℤ} (b : ℤ) (H : coprime c a) :
   gcd a (c * b) = gcd a b :=
!gcd.comm ▸ !gcd.comm ▸ !gcd_mul_left_cancel_of_coprime H

theorem gcd_mul_right_cancel_of_coprime_right {c a : ℤ} (b : ℤ) (H : coprime c a) :
   gcd a (b * c) = gcd a b :=
!gcd.comm ▸ !gcd.comm ▸ !gcd_mul_right_cancel_of_coprime H

theorem coprime_div_gcd_div_gcd {a b : ℤ} (H : gcd a b ≠ 0) :
  coprime (a div gcd a b) (b div gcd a b) :=
calc
  gcd (a div gcd a b) (b div gcd a b)
         = gcd a b div abs (gcd a b)  : gcd_div !gcd_dvd_left !gcd_dvd_right
     ... = 1                          : by rewrite [abs_of_nonneg !gcd_nonneg, div_self H]

theorem exists_coprime {a b : ℤ} (H : gcd a b ≠ 0) :
  exists a' b', coprime a' b' ∧ a = a' * gcd a b ∧ b = b' * gcd a b :=
have H1 : a = (a div gcd a b) * gcd a b, from (div_mul_cancel !gcd_dvd_left)⁻¹,
have H2 : b = (b div gcd a b) * gcd a b, from (div_mul_cancel !gcd_dvd_right)⁻¹,
exists.intro _ (exists.intro _ (and.intro (coprime_div_gcd_div_gcd H) (and.intro H1 H2)))

theorem coprime_mul {a b c : ℤ} (H1 : coprime a c) (H2 : coprime b c) : coprime (a * b) c :=
calc
  gcd (a * b) c = gcd b c : !gcd_mul_left_cancel_of_coprime H1
            ... = 1       : H2

theorem coprime_mul_right {c a b : ℤ} (H1 : coprime c a) (H2 : coprime c b) : coprime c (a * b) :=
coprime_swap (coprime_mul (coprime_swap H1) (coprime_swap H2))

theorem coprime_of_coprime_mul_left {c a b : ℤ} (H : coprime (c * a) b) : coprime a b :=
have H1 : (gcd a b ∣ gcd (c * a) b), from !gcd_dvd_gcd_mul_left,
eq_one_of_dvd_one !gcd_nonneg (H ▸ H1)

theorem coprime_of_coprime_mul_right {c a b : ℤ} (H : coprime (a * c) b) : coprime a b :=
coprime_of_coprime_mul_left (!mul.comm ▸ H)

theorem coprime_of_coprime_mul_left_right {c a b : ℤ} (H : coprime a (c * b)) : coprime a b :=
coprime_swap (coprime_of_coprime_mul_left (coprime_swap H))

theorem coprime_of_coprime_mul_right_right {c a b : ℤ} (H : coprime a (b * c)) : coprime a b :=
coprime_of_coprime_mul_left_right (!mul.comm ▸ H)

theorem exists_eq_prod_and_dvd_and_dvd {a b c} (H : c ∣ a * b) :
  ∃ a' b', c = a' * b' ∧ a' ∣ a ∧ b' ∣ b :=
decidable.by_cases
 (suppose gcd c a = 0,
    have c = 0, from eq_zero_of_gcd_eq_zero_left `gcd c a = 0`,
    have a = 0, from eq_zero_of_gcd_eq_zero_right `gcd c a = 0`,
    have c = 0 * b, from `c = 0` ⬝ !zero_mul⁻¹,
    have 0 ∣ a, from `a = 0`⁻¹ ▸ !dvd.refl,
    have b ∣ b, from !dvd.refl,
    exists.intro _ (exists.intro _ (and.intro `c = 0 * b` (and.intro `0 ∣ a` `b ∣ b`))))
  (suppose gcd c a ≠ 0,
    have gcd c a ∣ c, from !gcd_dvd_left,
    have H3 : c div gcd c a ∣ (a * b) div gcd c a, from div_dvd_div this H,
    have H4 : (a * b) div gcd c a = (a div gcd c a) * b, from
      calc
        a * b div gcd c a = b * a div gcd c a   : mul.comm
                      ... = b * (a div gcd c a) : !mul_div_assoc !gcd_dvd_right
                      ... = a div gcd c a * b   : mul.comm,
    have H5 : c div gcd c a ∣ (a div gcd c a) * b, from H4 ▸ H3,
    have H6 : coprime (c div gcd c a) (a div gcd c a), from coprime_div_gcd_div_gcd `gcd c a ≠ 0`,
    have H7 : c div gcd c a ∣ b, from dvd_of_coprime_of_dvd_mul_left H6 H5,
    have H8 : c = gcd c a * (c div gcd c a), from (mul_div_cancel' `gcd c a ∣ c`)⁻¹,
    exists.intro _ (exists.intro _ (and.intro H8 (and.intro !gcd_dvd_right H7))))

end int
