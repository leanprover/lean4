/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.nat.div
Authors: Jeremy Avigad, Leonardo de Moura

Definitions and properties of div, mod, gcd, lcm, coprime. Much of the development follows
Isabelle's library.
-/

import data.nat.sub tools.fake_simplifier
open eq.ops well_founded decidable fake_simplifier prod

namespace nat

/- div and mod -/

-- auxiliary lemma used to justify div
private definition div_rec_lemma {x y : nat} (H : 0 < y ∧ y ≤ x) : x - y < x :=
and.rec_on H (λ ypos ylex, sub_lt (lt_of_lt_of_le ypos ylex) ypos)

private definition div.F (x : nat) (f : Π x₁, x₁ < x → nat → nat) (y : nat) : nat :=
if H : 0 < y ∧ y ≤ x then f (x - y) (div_rec_lemma H) y + 1 else zero

definition divide (x y : nat) := fix div.F x y

theorem divide_def (x y : nat) : divide x y = if 0 < y ∧ y ≤ x then divide (x - y) y + 1 else 0 :=
congr_fun (fix_eq div.F x) y

notation a div b := divide a b

theorem div_zero (a : ℕ) : a div 0 = 0 :=
divide_def a 0 ⬝ if_neg (!not_and_of_not_left (lt.irrefl 0))

theorem div_eq_zero_of_lt {a b : ℕ} (h : a < b) : a div b = 0 :=
divide_def a b ⬝ if_neg (!not_and_of_not_right (not_le_of_lt h))

theorem zero_div (b : ℕ) : 0 div b = 0 :=
divide_def 0 b ⬝ if_neg (λ h, and.rec_on h (λ l r, absurd (lt_of_lt_of_le l r) (lt.irrefl 0)))

theorem div_eq_succ_sub_div {a b : ℕ} (h₁ : b > 0) (h₂ : a ≥ b) : a div b = succ ((a - b) div b) :=
divide_def a b ⬝ if_pos (and.intro h₁ h₂)

theorem add_div_self (x : ℕ) {z : ℕ} (H : z > 0) : (x + z) div z = succ (x div z) :=
calc
  (x + z) div z = if 0 < z ∧ z ≤ x + z then (x + z - z) div z + 1 else 0 : !divide_def
            ... = (x + z - z) div z + 1 : if_pos (and.intro H (le_add_left z x))
            ... = succ (x div z)        : {!add_sub_cancel}

theorem add_div_self_left {x : ℕ} (z : ℕ) (H : x > 0) : (x + z) div x = succ (z div x) :=
!add.comm ▸ !add_div_self H

theorem add_mul_div_self {x y z : ℕ} (H : z > 0) : (x + y * z) div z = x div z + y :=
nat.induction_on y
  (calc (x + zero * z) div z = (x + zero) div z : zero_mul
                       ...   = x div z          : add_zero
                       ...   = x div z + zero   : add_zero)
  (take y,
    assume IH : (x + y * z) div z = x div z + y, calc
      (x + succ y * z) div z = (x + y * z + z) div z    : by simp
                         ... = succ ((x + y * z) div z) : !add_div_self H
                         ... = x div z + succ y         : by simp)

theorem add_mul_div_self_left (x z : ℕ) {y : ℕ} (H : y > 0) : (x + y * z) div y = x div y + z :=
!mul.comm ▸ add_mul_div_self H

theorem mul_div_cancel (m : ℕ) {n : ℕ} (H : n > 0) : m * n div n = m :=
calc
  m * n div n = (0 + m * n) div n : zero_add
          ... = 0 div n + m       : add_mul_div_self H
          ... = 0 + m             : zero_div
          ... = m                 : zero_add

theorem mul_div_cancel_left {m : ℕ} (n : ℕ) (H : m > 0) : m * n div m = n :=
!mul.comm ▸ !mul_div_cancel H

private definition mod.F (x : nat) (f : Π x₁, x₁ < x → nat → nat) (y : nat) : nat :=
if H : 0 < y ∧ y ≤ x then f (x - y) (div_rec_lemma H) y else x

definition modulo (x y : nat) := fix mod.F x y

notation a mod b := modulo a b

theorem modulo_def (x y : nat) : modulo x y = if 0 < y ∧ y ≤ x then modulo (x - y) y else x :=
congr_fun (fix_eq mod.F x) y

theorem mod_zero (a : ℕ) : a mod 0 = a :=
modulo_def a 0 ⬝ if_neg (!not_and_of_not_left (lt.irrefl 0))

theorem mod_eq_of_lt {a b : ℕ} (h : a < b) : a mod b = a :=
modulo_def a b ⬝ if_neg (!not_and_of_not_right (not_le_of_lt h))

theorem zero_mod (b : ℕ) : 0 mod b = 0 :=
modulo_def 0 b ⬝ if_neg (λ h, and.rec_on h (λ l r, absurd (lt_of_lt_of_le l r) (lt.irrefl 0)))

theorem mod_eq_sub_mod {a b : ℕ} (h₁ : b > 0) (h₂ : a ≥ b) : a mod b = (a - b) mod b :=
modulo_def a b ⬝ if_pos (and.intro h₁ h₂)

theorem add_mod_self {x z : ℕ} (H : z > 0) : (x + z) mod z = x mod z :=
calc
  (x + z) mod z = if 0 < z ∧ z ≤ x + z then (x + z - z) mod z else _ : modulo_def
            ... = (x + z - z) mod z   : if_pos (and.intro H (le_add_left z x))
            ... = x mod z             : add_sub_cancel

theorem add_mod_self_left {x z : ℕ} (H : x > 0) : (x + z) mod x = z mod x :=
!add.comm ▸ add_mod_self H

theorem add_mul_mod_self {x y z : ℕ} (H : z > 0) : (x + y * z) mod z = x mod z :=
nat.induction_on y
  (calc (x + zero * z) mod z = (x + zero) mod z : zero_mul
                         ... = x mod z          : add_zero)
  (take y,
    assume IH : (x + y * z) mod z = x mod z,
    calc
      (x + succ y * z) mod z = (x + (y * z + z)) mod z : succ_mul
                         ... = (x + y * z + z) mod z   : add.assoc
                         ... = (x + y * z) mod z       : add_mod_self H
                         ... = x mod z                 : IH)

theorem add_mul_mod_self_left {x y z : ℕ} (H : y > 0) : (x + y * z) mod y = x mod y :=
!mul.comm ▸ add_mul_mod_self H

theorem mul_mod_left {m n : ℕ} : (m * n) mod n = 0 :=
by_cases_zero_pos n (by simp)
  (take n,
    assume npos : n > 0,
    (by simp) ▸ (@add_mul_mod_self 0 m _ npos))

theorem mul_mod_right {m n : ℕ} : (m * n) mod m = 0 :=
!mul.comm ▸ !mul_mod_left

theorem mod_lt {x y : ℕ} (H : y > 0) : x mod y < y :=
nat.case_strong_induction_on x
  (show 0 mod y < y, from !zero_mod⁻¹ ▸ H)
  (take x,
    assume IH : ∀x', x' ≤ x → x' mod y < y,
    show succ x mod y < y, from
      by_cases -- (succ x < y)
        (assume H1 : succ x < y,
          have H2 : succ x mod y = succ x, from mod_eq_of_lt H1,
          show succ x mod y < y, from H2⁻¹ ▸ H1)
        (assume H1 : ¬ succ x < y,
          have H2 : y ≤ succ x, from le_of_not_lt H1,
          have H3 : succ x mod y = (succ x - y) mod y, from mod_eq_sub_mod H H2,
          have H4 : succ x - y < succ x, from sub_lt !succ_pos H,
          have H5 : succ x - y ≤ x, from le_of_lt_succ H4,
          show succ x mod y < y, from H3⁻¹ ▸ IH _ H5))

/- properties of div and mod together -/

-- the quotient / remainder theorem
theorem eq_div_mul_add_mod {x y : ℕ} : x = x div y * y + x mod y :=
by_cases_zero_pos y
  (show x = x div 0 * 0 + x mod 0, from
    (calc
      x div 0 * 0 + x mod 0 = 0 + x mod 0 : mul_zero
        ... = x mod 0                     : zero_add
        ... = x                           : mod_zero)⁻¹)
  (take y,
    assume H : y > 0,
    show x = x div y * y + x mod y, from
      nat.case_strong_induction_on x
        (show 0 = (0 div y) * y + 0 mod y, by simp)
        (take x,
          assume IH : ∀x', x' ≤ x → x' = x' div y * y + x' mod y,
          show succ x = succ x div y * y + succ x mod y, from
            by_cases -- (succ x < y)
              (assume H1 : succ x < y,
                have H2 : succ x div y = 0, from div_eq_zero_of_lt H1,
                have H3 : succ x mod y = succ x, from mod_eq_of_lt H1,
                by simp)
              (assume H1 : ¬ succ x < y,
                have H2 : y ≤ succ x, from le_of_not_lt H1,
                have H3 : succ x div y = succ ((succ x - y) div y), from div_eq_succ_sub_div H H2,
                have H4 : succ x mod y = (succ x - y) mod y, from mod_eq_sub_mod H H2,
                have H5 : succ x - y < succ x, from sub_lt !succ_pos H,
                have H6 : succ x - y ≤ x, from le_of_lt_succ H5,
                (calc
                  succ x div y * y + succ x mod y =
                          succ ((succ x - y) div y) * y + succ x mod y      : H3
                    ... = ((succ x - y) div y) * y + y + succ x mod y       : succ_mul
                    ... = ((succ x - y) div y) * y + y + (succ x - y) mod y : H4
                    ... = ((succ x - y) div y) * y + (succ x - y) mod y + y : add.right_comm
                    ... = succ x - y + y                                    : {!(IH _ H6)⁻¹}
                    ... = succ x                                         : sub_add_cancel H2)⁻¹)))

theorem mod_le {x y : ℕ} : x mod y ≤ x :=
eq_div_mul_add_mod⁻¹ ▸ !le_add_left

theorem eq_remainder {y : ℕ} (H : y > 0) {q1 r1 q2 r2 : ℕ} (H1 : r1 < y) (H2 : r2 < y)
  (H3 : q1 * y + r1 = q2 * y + r2) : r1 = r2 :=
calc
  r1 = r1 mod y : by simp
    ... = (r1 + q1 * y) mod y : (add_mul_mod_self H)⁻¹
    ... = (q1 * y + r1) mod y : add.comm
    ... = (r2 + q2 * y) mod y : by simp
    ... = r2 mod y            : add_mul_mod_self H
    ... = r2                  : by simp

theorem eq_quotient {y : ℕ} (H : y > 0) {q1 r1 q2 r2 : ℕ} (H1 : r1 < y) (H2 : r2 < y)
  (H3 : q1 * y + r1 = q2 * y + r2) : q1 = q2 :=
have H4 : q1 * y + r2 = q2 * y + r2, from (eq_remainder H H1 H2 H3) ▸ H3,
have H5 : q1 * y = q2 * y, from add.cancel_right H4,
have H6 : y > 0, from lt_of_le_of_lt !zero_le H1,
show q1 = q2, from eq_of_mul_eq_mul_right H6 H5

theorem mul_div_mul_left {z : ℕ} (x y : ℕ) (zpos : z > 0) : (z * x) div (z * y) = x div y :=
by_cases -- (y = 0)
  (assume H : y = 0, by simp)
  (assume H : y ≠ 0,
    have ypos : y > 0, from pos_of_ne_zero H,
    have zypos : z * y > 0, from mul_pos zpos ypos,
    have H1 : (z * x) mod (z * y) < z * y, from mod_lt zypos,
    have H2 : z * (x mod y) < z * y, from mul_lt_mul_of_pos_left (mod_lt ypos) zpos,
    eq_quotient zypos H1 H2
      (calc
        ((z * x) div (z * y)) * (z * y) + (z * x) mod (z * y) = z * x : eq_div_mul_add_mod
          ... = z * (x div y * y + x mod y)                           : eq_div_mul_add_mod
          ... = z * (x div y * y) + z * (x mod y)                     : mul.left_distrib
          ... = (x div y) * (z * y) + z * (x mod y)                   : mul.left_comm))

theorem mul_div_mul_right {x z y : ℕ} (zpos : z > 0) : (x * z) div (y * z) = x div y :=
!mul.comm ▸ !mul.comm ▸ !mul_div_mul_left zpos

theorem mul_mod_mul_left (z x y : ℕ) : (z * x) mod (z * y) = z * (x mod y) :=
or.elim (eq_zero_or_pos z)
  (assume H : z = 0,
    calc
      (z * x) mod (z * y) = (0 * x) mod (z * y) : H
                      ... = 0 mod (z * y)       : zero_mul
                      ... = 0                   : zero_mod
                      ... = 0 * (x mod y)       : zero_mul
                      ... = z * (x mod y)       : H)
  (assume zpos : z > 0,
    or.elim (eq_zero_or_pos y)
      (assume H : y = 0, by simp)
      (assume ypos : y > 0,
        have zypos : z * y > 0, from mul_pos zpos ypos,
        have H1 : (z * x) mod (z * y) < z * y, from mod_lt zypos,
        have H2 : z * (x mod y) < z * y, from mul_lt_mul_of_pos_left (mod_lt ypos) zpos,
        eq_remainder zypos H1 H2
          (calc
            ((z * x) div (z * y)) * (z * y) + (z * x) mod (z * y) = z * x : eq_div_mul_add_mod
              ... = z * (x div y * y + x mod y)                           : eq_div_mul_add_mod
              ... = z * (x div y * y) + z * (x mod y)                     : mul.left_distrib
              ... = (x div y) * (z * y) + z * (x mod y)                   : mul.left_comm)))

theorem mul_mod_mul_right (x z y : ℕ) : (x * z) mod (y * z) = (x mod y) * z :=
mul.comm z x ▸ mul.comm z y ▸ !mul.comm ▸ !mul_mod_mul_left

theorem mod_one (n : ℕ) : n mod 1 = 0 :=
have H1 : n mod 1 < 1, from mod_lt !succ_pos,
eq_zero_of_le_zero (le_of_lt_succ H1)

theorem mod_self (n : ℕ) : n mod n = 0 :=
nat.cases_on n (by simp)
  (take n,
    have H : (succ n * 1) mod (succ n * 1) = succ n * (1 mod 1),
      from !mul_mod_mul_left,
    (by simp) ▸ H)

theorem div_one (n : ℕ) : n div 1 = n :=
have H : n div 1 * 1 + n mod 1 = n, from eq_div_mul_add_mod⁻¹,
(by simp) ▸ H

theorem div_self {n : ℕ} (H : n > 0) : n div n = 1 :=
have H1 : (n * 1) div (n * 1) = 1 div 1, from !mul_div_mul_left H,
(by simp) ▸ H1

theorem div_mul_cancel_of_mod_eq_zero {m n : ℕ} (H : m mod n = 0) : m div n * n = m :=
(calc
  m = m div n * n + m mod n : eq_div_mul_add_mod
    ... = m div n * n + 0 : H
    ... = m div n * n : !add_zero)⁻¹

theorem mul_div_cancel_of_mod_eq_zero {m n : ℕ} (H : m mod n = 0) : n * (m div n) = m :=
!mul.comm ▸ div_mul_cancel_of_mod_eq_zero H

theorem div_lt_of_lt_mul {m n k : ℕ} (H : m < k * n) : m div k < n :=
lt_of_mul_lt_mul_right (calc
  m div k * k ≤ m div k * k + m mod k : le_add_right
    ... = m                           : eq_div_mul_add_mod
    ... < k * n                       : H
    ... = n * k                       : nat.mul.comm)

theorem div_le_of_le_mul {m n k : ℕ} (H : m ≤ k * n) : m div k ≤ n :=
or.elim (eq_zero_or_pos k)
  (assume H1 : k = 0,
    calc
      m div k = m div 0 : H1
          ... = 0       : div_zero
          ... ≤ n       : zero_le)
  (assume H1 : k > 0,
    le_of_mul_le_mul_right (calc
      m div k * k ≤ m div k * k + m mod k : le_add_right
        ... = m                           : eq_div_mul_add_mod
        ... ≤ k * n                       : H
        ... = n * k                       : nat.mul.comm) H1)

theorem div_le (m n : ℕ) : m div n ≤ m :=
nat.cases_on n (!div_zero⁻¹ ▸ !zero_le)
  take n,
  have H : m ≤ succ n * m, from calc
        m = 1 * m      : one_mul
      ... ≤ succ n * m : mul_le_mul_right (succ_le_succ !zero_le),
  div_le_of_le_mul H

theorem mul_sub_div_of_lt {m n k : ℕ} (H : k < m * n) :
  (m * n - (k + 1)) div m = n - k div m - 1 :=
have H1 : k div m < n, from div_lt_of_lt_mul H,
have H2 : n - k div m ≥ 1, from
  le_sub_of_add_le (calc
    1 + k div m = succ (k div m) : add.comm
            ... ≤ n              : succ_le_of_lt H1),
assert H3 : n - k div m = n - k div m - 1 + 1, from (sub_add_cancel H2)⁻¹,
assert H4 : m > 0, from pos_of_ne_zero (assume H': m = 0, not_lt_zero _ (!zero_mul ▸ H' ▸ H)),
have H5   : k mod m + 1 ≤ m, from succ_le_of_lt (mod_lt H4),
assert H6 : m - (k mod m + 1) < m, from sub_lt_self H4 !succ_pos,
calc
  (m * n - (k + 1)) div m = (m * n - (k div m * m + k mod m + 1)) div m : eq_div_mul_add_mod
     ... = (m * n - k div m * m - (k mod m + 1)) div m                  : by rewrite [*sub_sub]
     ... = ((n - k div m) * m - (k mod m + 1)) div m                    :
               by rewrite [mul.comm m, mul_sub_right_distrib]
     ... = ((n - k div m - 1) * m + m - (k mod m + 1)) div m            :
               by rewrite [H3 at {1}, mul.right_distrib, nat.one_mul]
     ... = ((n - k div m - 1) * m + (m - (k mod m + 1))) div m          : {add_sub_assoc H5 _}
     ... = (m - (k mod m + 1)) div m + (n - k div m - 1)                :
               by rewrite [add.comm, (add_mul_div_self H4)]
     ... = n - k div m - 1                                              :
               by rewrite [div_eq_zero_of_lt H6, zero_add]

/- divides -/

theorem dvd_of_mod_eq_zero {m n : ℕ} (H : n mod m = 0) : (m | n) :=
dvd.intro (!mul.comm ▸ div_mul_cancel_of_mod_eq_zero H)

theorem mod_eq_zero_of_dvd {m n : ℕ} (H : (m | n)) : n mod m = 0 :=
dvd.elim H
  (take z,
    assume H1 : n = m * z,
    H1⁻¹ ▸ !mul_mod_right)

theorem dvd_iff_mod_eq_zero (m n : ℕ) : (m | n) ↔ n mod m = 0 :=
iff.intro mod_eq_zero_of_dvd dvd_of_mod_eq_zero

definition dvd.decidable_rel [instance] : decidable_rel dvd :=
take m n, decidable_of_decidable_of_iff _ (iff.symm !dvd_iff_mod_eq_zero)

theorem div_mul_cancel {m n : ℕ} (H : (n | m)) : m div n * n = m :=
div_mul_cancel_of_mod_eq_zero (mod_eq_zero_of_dvd H)

theorem mul_div_cancel' {m n : ℕ} (H : (n | m)) : n * (m div n) = m :=
!mul.comm ▸ div_mul_cancel H

theorem eq_mul_of_div_eq {m n k : ℕ} (H1 : (m | n)) (H2 : n div m = k) : n = m * k :=
eq.symm (calc
  m * k = m * (n div m) : H2
    ... = n             : mul_div_cancel' H1)

theorem eq_div_of_mul_eq {m n k : ℕ} (H1 : k > 0) (H2 : n * k = m) : n = m div k :=
calc
  n = n * k div k : mul_div_cancel _ H1
    ... = m div k : H2

theorem dvd_of_dvd_add_left {m n₁ n₂ : ℕ} (H₁ : (m | n₁ + n₂)) (H₂ : (m | n₁)) : (m | n₂) :=
obtain (c₁ : nat) (Hc₁ : n₁ + n₂ = m * c₁), from H₁,
obtain (c₂ : nat) (Hc₂ : n₁ = m * c₂), from H₂,
have   aux : m * (c₁ - c₂) = n₂, from calc
  m * (c₁ - c₂) = m * c₁  - m * c₂ : mul_sub_left_distrib
           ...  = n₁ + n₂ - m * c₂ : Hc₁
           ...  = n₁ + n₂ - n₁     : Hc₂
           ...  = n₂               : add_sub_cancel_left,
dvd.intro aux

theorem dvd_of_dvd_add_right {m n1 n2 : ℕ} (H : (m | (n1 + n2))) : (m | n2) → (m | n1) :=
dvd_of_dvd_add_left (!add.comm ▸ H)

theorem dvd_sub {m n1 n2 : ℕ} (H1 : (m | n1)) (H2 : (m | n2)) : (m | n1 - n2) :=
by_cases
  (assume H3 : n1 ≥ n2,
    have H4 : n1 = n1 - n2 + n2, from (sub_add_cancel H3)⁻¹,
    show (m | n1 - n2), from dvd_of_dvd_add_right (H4 ▸ H1) H2)
  (assume H3 : ¬ (n1 ≥ n2),
    have H4 : n1 - n2 = 0, from sub_eq_zero_of_le (le_of_lt (lt_of_not_le H3)),
    show (m | n1 - n2), from H4⁻¹ ▸ dvd_zero _)

theorem dvd.antisymm {m n : ℕ} : (m | n) → (n | m) → m = n :=
by_cases_zero_pos n
  (assume H1, assume H2 : (0 | m), eq_zero_of_zero_dvd H2)
  (take n,
    assume Hpos : n > 0,
    assume H1 : (m | n),
    assume H2 : (n | m),
    obtain k (Hk : n = m * k), from exists_eq_mul_right_of_dvd H1,
    obtain l (Hl : m = n * l), from exists_eq_mul_right_of_dvd H2,
    have H3 : n * (l * k) = n, from !mul.assoc ▸ Hl ▸ Hk⁻¹,
    have H4 : l * k = 1, from eq_one_of_mul_eq_self_right Hpos H3,
    have H5 : k = 1, from eq_one_of_mul_eq_one_left H4,
    show m = n, from (mul_one m)⁻¹ ⬝ (H5 ▸ Hk⁻¹))

theorem mul_div_assoc (m : ℕ) {n k : ℕ} (H : (k | n)) : m * n div k = m * (n div k) :=
or.elim (eq_zero_or_pos k)
  (assume H1 : k = 0,
    calc
      m * n div k = m * n div 0   : H1
              ... = 0             : div_zero
              ... = m * 0         : mul_zero m
              ... = m * (n div 0) : div_zero
              ... = m * (n div k) : H1)
  (assume H1 : k > 0,
    have H2 : n = n div k * k, from (div_mul_cancel H)⁻¹,
      calc
        m * n div k = m * (n div k * k) div k : H2
                ... = m * (n div k) * k div k : mul.assoc
                ... = m * (n div k)           : mul_div_cancel _ H1)

theorem dvd_of_mul_dvd_mul_left {m n k : ℕ} (kpos : k > 0) (H : (k * m | k * n)) : (m | n) :=
dvd.elim H
  (take l,
    assume H1 : k * n = k * m * l,
    have H2 : n = m * l, from eq_of_mul_eq_mul_left kpos (H1 ⬝ !mul.assoc),
    dvd.intro H2⁻¹)

theorem dvd_of_mul_dvd_mul_right {m n k : ℕ} (kpos : k > 0) (H : (m * k | n * k)) : (m | n) :=
dvd_of_mul_dvd_mul_left kpos (!mul.comm ▸ !mul.comm ▸ H)

theorem div_dvd_div {k m n : ℕ} (H1 : (k | m)) (H2 : (m | n)) : (m div k | n div k) :=
have H3 : m = m div k * k, from (div_mul_cancel H1)⁻¹,
have H4 : n = n div k * k, from (div_mul_cancel (dvd.trans H1 H2))⁻¹,
or.elim (eq_zero_or_pos k)
  (assume H5 : k = 0,
    have H6: n div k = 0, from (congr_arg _ H5 ⬝ !div_zero),
      H6⁻¹ ▸ !dvd_zero)
  (assume H5 : k > 0,
    dvd_of_mul_dvd_mul_right H5 (H3 ▸ H4 ▸ H2))

/- gcd -/

private definition pair_nat.lt : nat × nat → nat × nat → Prop := measure pr₂
private definition pair_nat.lt.wf : well_founded pair_nat.lt :=
intro_k (measure.wf pr₂) 20  -- we use intro_k to be able to execute gcd efficiently in the kernel

local attribute pair_nat.lt.wf [instance]      -- instance will not be saved in .olean
local infixl `≺`:50 := pair_nat.lt

private definition gcd.lt.dec (x y₁ : nat) : (succ y₁, x mod succ y₁) ≺ (x, succ y₁) :=
mod_lt (succ_pos y₁)

definition gcd.F (p₁ : nat × nat) : (Π p₂ : nat × nat, p₂ ≺ p₁ → nat) → nat :=
prod.cases_on p₁ (λx y, nat.cases_on y
  (λ f, x)
  (λ y₁ (f : Πp₂, p₂ ≺ (x, succ y₁) → nat), f (succ y₁, x mod succ y₁) !gcd.lt.dec))

definition gcd (x y : nat) := fix gcd.F (pair x y)

theorem gcd_zero_right (x : nat) : gcd x 0 = x :=
well_founded.fix_eq gcd.F (x, 0)

theorem gcd_succ (x y : nat) : gcd x (succ y) = gcd (succ y) (x mod succ y) :=
well_founded.fix_eq gcd.F (x, succ y)

theorem gcd_one_right (n : ℕ) : gcd n 1 = 1 :=
calc gcd n 1 = gcd 1 (n mod 1) : gcd_succ n zero
         ... = gcd 1 0         : mod_one
         ... = 1               : gcd_zero_right

theorem gcd_def (x y : ℕ) : gcd x y = if y = 0 then x else gcd y (x mod y) :=
nat.cases_on y
  (calc gcd x 0 = x                                          : gcd_zero_right x
           ...  = if 0 = 0 then x else gcd zero (x mod zero) : (if_pos rfl)⁻¹)
  (λy₁, calc
    gcd x (succ y₁) = gcd (succ y₁) (x mod succ y₁)                  : gcd_succ x y₁
      ... = if succ y₁ = 0 then x else gcd (succ y₁) (x mod succ y₁) : (if_neg (succ_ne_zero y₁))⁻¹)

theorem gcd_self (n : ℕ) : gcd n n = n :=
nat.cases_on n
  rfl
  (λn₁, calc
    gcd (succ n₁) (succ n₁) = gcd (succ n₁) (succ n₁ mod succ n₁) : gcd_succ (succ n₁) n₁
                      ...   = gcd (succ n₁) 0                     : mod_self (succ n₁)
                      ...   = succ n₁                             : gcd_zero_right)

theorem gcd_zero_left (n : nat) : gcd 0 n = n :=
nat.cases_on n
  rfl
  (λ n₁, calc
    gcd 0 (succ n₁) = gcd (succ n₁) (0 mod succ n₁) : gcd_succ
                ... = gcd (succ n₁) 0               : zero_mod
                ... = (succ n₁)                     : gcd_zero_right)

theorem gcd_rec_of_pos (m : ℕ) {n : ℕ} (H : n > 0) : gcd m n = gcd n (m mod n) :=
gcd_def m n ⬝ if_neg (ne_zero_of_pos H)

theorem gcd_rec (m n : ℕ) : gcd m n = gcd n (m mod n) :=
by_cases_zero_pos n
  (calc
    gcd m 0 = m               : gcd_zero_right
        ... = gcd 0 m         : gcd_zero_left
        ... = gcd 0 (m mod 0) : mod_zero)
  (take n, assume H : 0 < n, gcd_rec_of_pos m H)

theorem gcd.induction {P : ℕ → ℕ → Prop}
                   (m n : ℕ)
                   (H0 : ∀m, P m 0)
                   (H1 : ∀m n, 0 < n → P n (m mod n) → P m n) :
                 P m n :=
let Q : nat × nat → Prop := λ p : nat × nat, P (pr₁ p) (pr₂ p) in
have aux : Q (m, n), from
  well_founded.induction (m, n) (λp, prod.cases_on p
    (λm n, nat.cases_on n
      (λ ih, show P (pr₁ (m, 0)) (pr₂ (m, 0)), from H0 m)
      (λ n₁ (ih : ∀p₂, p₂ ≺ (m, succ n₁) → P (pr₁ p₂) (pr₂ p₂)),
        have hlt₁ : 0 < succ n₁, from succ_pos n₁,
        have hlt₂ : (succ n₁, m mod succ n₁) ≺ (m, succ n₁), from gcd.lt.dec _ _,
        have hp   : P (succ n₁) (m mod succ n₁), from ih _ hlt₂,
        show P m (succ n₁), from
          H1 m (succ n₁) hlt₁ hp))),
aux

theorem gcd_dvd (m n : ℕ) : (gcd m n | m) ∧ (gcd m n | n) :=
gcd.induction m n
  (take m,
    show (gcd m 0 | m) ∧ (gcd m 0 | 0), by simp)
  (take m n,
    assume npos : 0 < n,
    assume IH : (gcd n (m mod n) | n) ∧ (gcd n (m mod n) | (m mod n)),
    have H : (gcd n (m mod n) | (m div n * n + m mod n)), from
      dvd_add (dvd.trans (and.elim_left IH) !dvd_mul_left) (and.elim_right IH),
    have H1 : (gcd n (m mod n) | m), from eq_div_mul_add_mod⁻¹ ▸ H,
    have gcd_eq : gcd n (m mod n) = gcd m n, from !gcd_rec⁻¹,
    show (gcd m n | m) ∧ (gcd m n | n), from gcd_eq ▸ (and.intro H1 (and.elim_left IH)))

theorem gcd_dvd_left (m n : ℕ) : (gcd m n | m) := and.elim_left !gcd_dvd

theorem gcd_dvd_right (m n : ℕ) : (gcd m n | n) := and.elim_right !gcd_dvd

theorem dvd_gcd {m n k : ℕ} : (k | m) → (k | n) → (k | gcd m n) :=
gcd.induction m n
  (take m, assume (h₁ : (k | m)) (h₂ : (k | 0)),
   show (k | gcd m 0), from !gcd_zero_right⁻¹ ▸ h₁)
  (take m n,
    assume npos : n > 0,
    assume IH : (k | n) → (k | m mod n) → (k | gcd n (m mod n)),
    assume H1 : (k | m),
    assume H2 : (k | n),
    have H3 : (k | m div n * n + m mod n), from eq_div_mul_add_mod ▸ H1,
    have H4 : (k | m mod n), from nat.dvd_of_dvd_add_left H3 (dvd.trans H2 (by simp)),
    have gcd_eq : gcd n (m mod n) = gcd m n, from !gcd_rec⁻¹,
    show (k | gcd m n), from gcd_eq ▸ IH H2 H4)

theorem gcd.comm (m n : ℕ) : gcd m n = gcd n m :=
dvd.antisymm
  (dvd_gcd !gcd_dvd_right !gcd_dvd_left)
  (dvd_gcd !gcd_dvd_right !gcd_dvd_left)

theorem gcd.assoc (m n k : ℕ) : gcd (gcd m n) k = gcd m (gcd n k) :=
dvd.antisymm
  (dvd_gcd
    (dvd.trans !gcd_dvd_left !gcd_dvd_left)
    (dvd_gcd (dvd.trans !gcd_dvd_left !gcd_dvd_right) !gcd_dvd_right))
  (dvd_gcd
    (dvd_gcd !gcd_dvd_left (dvd.trans !gcd_dvd_right !gcd_dvd_left))
    (dvd.trans !gcd_dvd_right !gcd_dvd_right))

theorem gcd_one_left (m : ℕ) : gcd 1 m = 1 :=
!gcd.comm ⬝ !gcd_one_right

theorem gcd_mul_left (m n k : ℕ) : gcd (m * n) (m * k) = m * gcd n k :=
gcd.induction n k
  (take n,
    calc
      gcd (m * n) (m * 0) = gcd (m * n) 0 : mul_zero
                      ... = m * n         : gcd_zero_right
                      ... = m * gcd n 0   : gcd_zero_right)
  (take n k,
    assume H : 0 < k,
    assume IH : gcd (m * k) (m * (n mod k)) = m * gcd k (n mod k),
    calc
      gcd (m * n) (m * k) = gcd (m * k) (m * n mod (m * k)) : !gcd_rec
                      ... = gcd (m * k) (m * (n mod k))     : mul_mod_mul_left
                      ... = m * gcd k (n mod k)             : IH
                      ... = m * gcd n k                     : !gcd_rec)

theorem gcd_mul_right (m n k : ℕ) : gcd (m * n) (k * n) = gcd m k * n :=
calc
  gcd (m * n) (k * n) = gcd (n * m) (k * n) : mul.comm
                  ... = gcd (n * m) (n * k) : mul.comm
                  ... = n * gcd m k         : gcd_mul_left
                  ... = gcd m k * n         : mul.comm

theorem gcd_pos_of_pos_left {m : ℕ} (n : ℕ) (mpos : m > 0) : gcd m n > 0 :=
pos_of_dvd_of_pos !gcd_dvd_left mpos

theorem gcd_pos_of_pos_right (m : ℕ) {n : ℕ} (npos : n > 0) : gcd m n > 0 :=
pos_of_dvd_of_pos !gcd_dvd_right npos

theorem eq_zero_of_gcd_eq_zero_left {m n : ℕ} (H : gcd m n = 0) : m = 0 :=
or.elim (eq_zero_or_pos m)
  (assume H1, H1)
  (assume H1 : m > 0, absurd H⁻¹ (ne_of_lt (!gcd_pos_of_pos_left H1)))

theorem eq_zero_of_gcd_eq_zero_right {m n : ℕ} (H : gcd m n = 0) : n = 0 :=
eq_zero_of_gcd_eq_zero_left (!gcd.comm ▸ H)

theorem gcd_div {m n k : ℕ} (H1 : (k | m)) (H2 : (k | n)) : gcd (m div k) (n div k) = gcd m n div k :=
or.elim (eq_zero_or_pos k)
  (assume H3 : k = 0,
    calc
      gcd (m div k) (n div k) = gcd (m div 0) (n div k) : H3
                          ... = gcd 0 (n div k)         : div_zero
                          ... = n div k                 : gcd_zero_left
                          ... = n div 0                 : H3
                          ... = 0                       : div_zero
                          ... = gcd m n div 0           : div_zero
                          ... = gcd m n div k           : H3)
  (assume H3 : k > 0,
    eq_div_of_mul_eq H3
      (calc
        gcd (m div k) (n div k) * k = gcd (m div k * k) (n div k * k) : gcd_mul_right
                                ... = gcd m (n div k * k)             : div_mul_cancel H1
                                ... = gcd m n                         : div_mul_cancel H2))

theorem gcd_dvd_gcd_mul_left (m n k : ℕ) : (gcd m n | gcd (k * m) n) :=
dvd_gcd (dvd.trans !gcd_dvd_left !dvd_mul_left) !gcd_dvd_right

theorem gcd_dvd_gcd_mul_right (m n k : ℕ) : (gcd m n | gcd (m * k) n) :=
!mul.comm ▸ !gcd_dvd_gcd_mul_left

theorem gcd_dvd_gcd_mul_left_right (m n k : ℕ) : (gcd m n | gcd m (k * n)) :=
dvd_gcd  !gcd_dvd_left (dvd.trans !gcd_dvd_right !dvd_mul_left)

theorem gcd_dvd_gcd_mul_right_right (m n k : ℕ) : (gcd m n | gcd m (n * k)) :=
!mul.comm ▸ !gcd_dvd_gcd_mul_left_right

/- lcm -/

definition lcm (m n : ℕ) : ℕ := m * n div (gcd m n)

theorem lcm.comm (m n : ℕ) : lcm m n = lcm n m :=
calc
  lcm m n = m * n div gcd m n : rfl
      ... = n * m div gcd m n : mul.comm
      ... = n * m div gcd n m : gcd.comm
      ... = lcm n m           : rfl

theorem lcm_zero_left (m : ℕ) : lcm 0 m = 0 :=
calc
  lcm 0 m = 0 * m div gcd 0 m : rfl
      ... = 0 div gcd 0 m     : zero_mul
      ... = 0                 : zero_div

theorem lcm_zero_right (m : ℕ) : lcm m 0 = 0 := !lcm.comm ▸ !lcm_zero_left

theorem lcm_one_left (m : ℕ) : lcm 1 m = m :=
calc
  lcm 1 m = 1 * m div gcd 1 m : rfl
      ... = m div gcd 1 m     : one_mul
      ... = m div 1           : gcd_one_left
      ... = m                 : div_one

theorem lcm_one_right (m : ℕ) : lcm m 1 = m := !lcm.comm ▸ !lcm_one_left

theorem lcm_self (m : ℕ) : lcm m m = m :=
have H : m * m div m = m, from
  by_cases_zero_pos m !div_zero (take m, assume H1 : m > 0, !mul_div_cancel H1),
calc
  lcm m m = m * m div gcd m m : rfl
      ... = m * m div m       : gcd_self
      ... = m                 : H

theorem dvd_lcm_left (m n : ℕ) : (m | lcm m n) :=
have H : lcm m n = m * (n div gcd m n), from mul_div_assoc _ !gcd_dvd_right,
dvd.intro H⁻¹

theorem dvd_lcm_right (m n : ℕ) : (n | lcm m n) :=
!lcm.comm ▸ !dvd_lcm_left

theorem gcd_mul_lcm (m n : ℕ) : gcd m n * lcm m n = m * n :=
eq.symm (eq_mul_of_div_eq (dvd.trans !gcd_dvd_left !dvd_mul_right) rfl)

theorem lcm_dvd {m n k : ℕ} (H1 : (m | k)) (H2 : (n | k)) : (lcm m n | k) :=
or.elim (eq_zero_or_pos k)
  (assume kzero : k = 0, !kzero⁻¹ ▸ !dvd_zero)
  (assume kpos : k > 0,
    have mpos : m > 0, from pos_of_dvd_of_pos H1 kpos,
    have npos : n > 0, from pos_of_dvd_of_pos H2 kpos,
    have gcd_pos : gcd m n > 0, from !gcd_pos_of_pos_left mpos,
    obtain p (km : k = m * p), from exists_eq_mul_right_of_dvd H1,
    obtain q (kn : k = n * q), from exists_eq_mul_right_of_dvd H2,
    have ppos : p > 0, from pos_of_mul_pos_left (km ▸ kpos),
    have qpos : q > 0, from pos_of_mul_pos_left (kn ▸ kpos),
    have H3 : p * q * (m * n * gcd p q) = p * q * (gcd m n * k), from
    calc
      p * q * (m * n * gcd p q) = p * (q * (m * n * gcd p q)) : mul.assoc
        ... = p * (q * (m * (n * gcd p q)))                   : mul.assoc
        ... = p * (m * (q * (n * gcd p q)))                   : mul.left_comm
        ... = p * m * (q * (n * gcd p q))                     : mul.assoc
        ... = p * m * (q * n * gcd p q)                       : mul.assoc
        ... = m * p * (q * n * gcd p q)                       : mul.comm
        ... = k * (q * n * gcd p q)                           : km
        ... = k * (n * q * gcd p q)                           : mul.comm
        ... = k * (k * gcd p q)                               : kn
        ... = k * gcd (k * p) (k * q)                         : gcd_mul_left
        ... = k * gcd (n * q * p) (k * q)                     : kn
        ... = k * gcd (n * q * p) (m * p * q)                 : km
        ... = k * gcd (n * (q * p)) (m * p * q)               : mul.assoc
        ... = k * gcd (n * (q * p)) (m * (p * q))             : mul.assoc
        ... = k * gcd (n * (p * q)) (m * (p * q))             : mul.comm
        ... = k * (gcd n m * (p * q))                         : gcd_mul_right
        ... = gcd n m * (p * q) * k                           : mul.comm
        ... = p * q * gcd n m * k                             : mul.comm
        ... = p * q * (gcd n m * k)                           : mul.assoc
        ... = p * q * (gcd m n * k)                           : gcd.comm,
    have H4 : m * n * gcd p q = gcd m n * k,
      from !eq_of_mul_eq_mul_left (mul_pos ppos qpos) H3,
    have H5 : gcd m n * (lcm m n * gcd p q) = gcd m n * k,
      from !mul.assoc ▸ !gcd_mul_lcm⁻¹ ▸ H4,
    have H6 : lcm m n * gcd p q = k,
      from !eq_of_mul_eq_mul_left gcd_pos H5,
    dvd.intro H6)

theorem lcm_assoc (m n k : ℕ) : lcm (lcm m n) k = lcm m (lcm n k) :=
dvd.antisymm
  (lcm_dvd
    (lcm_dvd !dvd_lcm_left (dvd.trans !dvd_lcm_left !dvd_lcm_right))
    (dvd.trans !dvd_lcm_right !dvd_lcm_right))
  (lcm_dvd
    (dvd.trans !dvd_lcm_left !dvd_lcm_left)
    (lcm_dvd (dvd.trans !dvd_lcm_right !dvd_lcm_left) !dvd_lcm_right))

/- coprime -/

definition coprime [reducible] (m n : ℕ) : Prop := gcd m n = 1

theorem coprime_swap {m n : ℕ} (H : coprime n m) : coprime m n :=
!gcd.comm ▸ H

theorem dvd_of_coprime_of_dvd_mul_right {m n k : ℕ} (H1 : coprime k n) (H2 : (k | m * n)) : (k | m) :=
have H3 : gcd (m * k) (m * n) = m, from
  calc
    gcd (m * k) (m * n) = m * gcd k n : gcd_mul_left
                    ... = m * 1       : H1
                    ... = m           : mul_one,
have H4 : (k | gcd (m * k) (m * n)), from dvd_gcd !dvd_mul_left H2,
H3 ▸ H4

theorem dvd_of_coprime_of_dvd_mul_left {m n k : ℕ} (H1 : coprime k m) (H2 : (k | m * n)) : (k | n) :=
dvd_of_coprime_of_dvd_mul_right H1 (!mul.comm ▸ H2)

theorem gcd_mul_left_cancel_of_coprime {k : ℕ} (m : ℕ) {n : ℕ} (H : coprime k n) :
   gcd (k * m) n = gcd m n :=
have H1 : coprime (gcd (k * m) n) k, from
  calc
    gcd (gcd (k * m) n) k = gcd k (gcd (k * m) n)       : gcd.comm
                      ... = gcd (gcd k (k * m)) n       : gcd.assoc
                      ... = gcd (gcd (k * 1) (k * m)) n : mul_one
                      ... = gcd (k * gcd 1 m) n         : gcd_mul_left
                      ... = gcd (k * 1) n               : gcd_one_left
                      ... = gcd k n                     : mul_one
                      ... = 1 : H,
dvd.antisymm
  (dvd_gcd (dvd_of_coprime_of_dvd_mul_left H1 !gcd_dvd_left) !gcd_dvd_right)
  (dvd_gcd (dvd.trans !gcd_dvd_left !dvd_mul_left) !gcd_dvd_right)

theorem gcd_mul_right_cancel_of_coprime (m : ℕ) {k n : ℕ} (H : coprime k n) :
   gcd (m * k) n = gcd m n :=
!mul.comm ▸ !gcd_mul_left_cancel_of_coprime H

theorem gcd_mul_left_cancel_of_coprime_right {k m : ℕ} (n : ℕ) (H : coprime k m) :
   gcd m (k * n) = gcd m n :=
!gcd.comm ▸ !gcd.comm ▸ !gcd_mul_left_cancel_of_coprime H

theorem gcd_mul_right_cancel_of_coprime_right {k m : ℕ} (n : ℕ) (H : coprime k m) :
   gcd m (n * k) = gcd m n :=
!gcd.comm ▸ !gcd.comm ▸ !gcd_mul_right_cancel_of_coprime H

theorem coprime_div_gcd_div_gcd {m n : ℕ} (H : gcd m n > 0) :
  coprime (m div gcd m n) (n div gcd m n) :=
calc
  gcd (m div gcd m n) (n div gcd m n) = gcd m n div gcd m n : gcd_div !gcd_dvd_left !gcd_dvd_right
     ... = 1 : div_self H

theorem exists_coprime {m n : ℕ} (H : gcd m n > 0) :
  exists m' n', coprime m' n' ∧ m = m' * gcd m n ∧ n = n' * gcd m n :=
have H1 : m = (m div gcd m n) * gcd m n, from (div_mul_cancel !gcd_dvd_left)⁻¹,
have H2 : n = (n div gcd m n) * gcd m n, from (div_mul_cancel !gcd_dvd_right)⁻¹,
exists.intro _ (exists.intro _ (and.intro (coprime_div_gcd_div_gcd H) (and.intro H1 H2)))

theorem coprime_mul {m n k : ℕ} (H1 : coprime m k) (H2 : coprime n k) : coprime (m * n) k :=
calc
  gcd (m * n) k = gcd n k : !gcd_mul_left_cancel_of_coprime H1
            ... = 1       : H2

theorem coprime_mul_right {k m n : ℕ} (H1 : coprime k m) (H2 : coprime k n) : coprime k (m * n) :=
coprime_swap (coprime_mul (coprime_swap H1) (coprime_swap H2))

theorem coprime_of_coprime_mul_left {k m n : ℕ} (H : coprime (k * m) n) : coprime m n :=
have H1 : (gcd m n | gcd (k * m) n), from !gcd_dvd_gcd_mul_left,
eq_one_of_dvd_one (H ▸ H1)

theorem coprime_of_coprime_mul_right {k m n : ℕ} (H : coprime (m * k) n) : coprime m n :=
coprime_of_coprime_mul_left (!mul.comm ▸ H)

theorem coprime_of_coprime_mul_left_right {k m n : ℕ} (H : coprime m (k * n)) : coprime m n :=
coprime_swap (coprime_of_coprime_mul_left (coprime_swap H))

theorem coprime_of_coprime_mul_right_right {k m n : ℕ} (H : coprime m (n * k)) : coprime m n :=
coprime_of_coprime_mul_left_right (!mul.comm ▸ H)

theorem exists_eq_prod_and_dvd_and_dvd {m n k} (H : (k | m * n)) :
  ∃ m' n', k = m' * n' ∧ (m' | m) ∧ (n' | n) :=
or.elim (eq_zero_or_pos (gcd k m))
 (assume H1 : gcd k m = 0,
    have H2 : k = 0, from eq_zero_of_gcd_eq_zero_left H1,
    have H3 : m = 0, from eq_zero_of_gcd_eq_zero_right H1,
    have H4 : k = 0 * n, from H2 ⬝ !zero_mul⁻¹,
    have H5 : (0 | m), from H3⁻¹ ▸ !dvd.refl,
    have H6 : (n | n), from !dvd.refl,
    exists.intro _ (exists.intro _ (and.intro H4 (and.intro H5 H6))))
  (assume H1 : gcd k m > 0,
    have H2 : (gcd k m | k), from !gcd_dvd_left,
    have H3 : (k div gcd k m | (m * n) div gcd k m), from div_dvd_div H2 H,
    have H4 : (m * n) div gcd k m = (m div gcd k m) * n, from
      calc
        m * n div gcd k m = n * m div gcd k m   : mul.comm
                      ... = n * (m div gcd k m) : !mul_div_assoc !gcd_dvd_right
                      ... = m div gcd k m * n   : mul.comm,
    have H5 : (k div gcd k m | (m div gcd k m) * n), from H4 ▸ H3,
    have H6 : coprime (k div gcd k m) (m div gcd k m), from coprime_div_gcd_div_gcd H1,
    have H7 : (k div gcd k m | n), from dvd_of_coprime_of_dvd_mul_left H6 H5,
    have H8 : k = gcd k m * (k div gcd k m), from (mul_div_cancel' H2)⁻¹,
    exists.intro _ (exists.intro _ (and.intro H8 (and.intro !gcd_dvd_right H7))))

end nat
