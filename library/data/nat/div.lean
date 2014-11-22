--- Copyright (c) 2014 Jeremy Avigad. All rights reserved.
--- Released under Apache 2.0 license as described in the file LICENSE.
--- Author: Jeremy Avigad, Leonardo de Moura

-- div.lean
-- ========
--
-- This is a continuation of the development of the natural numbers, with a general way of
-- defining recursive functions, and definitions of div, mod, and gcd.

import data.nat.sub logic data.prod.wf
import algebra.relation
import tools.fake_simplifier

open eq.ops well_founded decidable fake_simplifier prod
open relation relation.iff_ops

namespace nat

-- Auxiliary lemma used to justify div
private definition div_rec_lemma {x y : nat} (H : 0 < y ∧ y ≤ x) : x - y < x :=
and.rec_on H (λ ypos ylex,
  sub.lt (lt_le.trans ypos ylex) ypos)

private definition div.F (x : nat) (f : Π x₁, x₁ < x → nat → nat) (y : nat) : nat :=
dif 0 < y ∧ y ≤ x then (λ Hp, f (x - y) (div_rec_lemma Hp) y + 1) else (λ Hn, zero)

definition divide (x y : nat) :=
fix div.F x y

theorem divide_def (x y : nat) : divide x y = if 0 < y ∧ y ≤ x then divide (x - y) y + 1 else 0 :=
congr_fun (fix_eq div.F x) y

notation a div b := divide a b

theorem div_zero (a : ℕ) : a div 0 = 0 :=
divide_def a 0 ⬝ if_neg (!and.not_left (lt.irrefl 0))

theorem div_less {a b : ℕ} (h : a < b) : a div b = 0 :=
divide_def a b ⬝ if_neg (!and.not_right (lt_imp_not_ge h))

theorem zero_div (b : ℕ) : 0 div b = 0 :=
divide_def 0 b ⬝ if_neg (λ h, and.rec_on h (λ l r, absurd (lt_le.trans l r) (lt.irrefl 0)))

theorem div_rec {a b : ℕ} (h₁ : b > 0) (h₂ : a ≥ b) : a div b = succ ((a - b) div b) :=
divide_def a b ⬝ if_pos (and.intro h₁ h₂)

theorem div_add_self_right {x z : ℕ} (H : z > 0) : (x + z) div z = succ (x div z) :=
calc (x + z) div z
    = if 0 < z ∧ z ≤ x + z then divide (x + z - z) z + 1 else 0 : !divide_def
... = divide (x + z - z) z + 1                                  : if_pos (and.intro H (le_add_left z x))
... = succ (x div z)                                            : sub_add_left

theorem div_add_mul_self_right {x y z : ℕ} (H : z > 0) : (x + y * z) div z = x div z + y :=
induction_on y (by simp)
  (take y,
    assume IH : (x + y * z) div z = x div z + y,
    calc
      (x + succ y * z) div z = (x + y * z + z) div z    : by simp
                         ... = succ ((x + y * z) div z) : div_add_self_right H
                         ... = x div z + succ y         : by simp)

private definition mod.F (x : nat) (f : Π x₁, x₁ < x → nat → nat) (y : nat) : nat :=
dif 0 < y ∧ y ≤ x then (λh, f (x - y) (div_rec_lemma h) y) else (λh, x)

definition modulo (x y : nat) :=
fix mod.F x y

notation a mod b := modulo a b

theorem modulo_def (x y : nat) : modulo x y = if 0 < y ∧ y ≤ x then modulo (x - y) y else x :=
congr_fun (fix_eq mod.F x) y

theorem mod_zero (a : ℕ) : a mod 0 = a :=
modulo_def a 0 ⬝ if_neg (!and.not_left (lt.irrefl 0))

theorem mod_less {a b : ℕ} (h : a < b) : a mod b = a :=
modulo_def a b ⬝ if_neg (!and.not_right (lt_imp_not_ge h))

theorem zero_mod (b : ℕ) : 0 mod b = 0 :=
modulo_def 0 b ⬝ if_neg (λ h, and.rec_on h (λ l r, absurd (lt_le.trans l r) (lt.irrefl 0)))

theorem mod_rec {a b : ℕ} (h₁ : b > 0) (h₂ : a ≥ b) : a mod b = (a - b) mod b :=
modulo_def a b ⬝ if_pos (and.intro h₁ h₂)

theorem mod_add_self_right {x z : ℕ} (H : z > 0) : (x + z) mod z = x mod z :=
calc (x + z) mod z
    = if 0 < z ∧ z ≤ x + z then (x + z - z) mod z else _ : !modulo_def
... = (x + z - z) mod z                                  : if_pos (and.intro H (le_add_left z x))
... = x mod z                                            : sub_add_left


theorem mod_add_mul_self_right {x y z : ℕ} (H : z > 0) : (x + y * z) mod z = x mod z :=
induction_on y
  (calc (x + zero * z) mod z = (x + zero) mod z : mul.zero_left
                         ... = x mod z          : add.zero_right)
  (take y,
    assume IH : (x + y * z) mod z = x mod z,
    calc
      (x + succ y * z) mod z = (x + (y * z + z)) mod z : mul.succ_left
                         ... = (x + y * z + z) mod z   : add.assoc
                         ... = (x + y * z) mod z       : mod_add_self_right H
                         ... = x mod z                 : IH)

theorem mod_mul_self_right {m n : ℕ} : (m * n) mod n = 0 :=
case_zero_pos n (by simp)
  (take n,
    assume npos : n > 0,
    (by simp) ▸ (@mod_add_mul_self_right 0 m _ npos))

-- add_rewrite mod_mul_self_right

theorem mod_mul_self_left {m n : ℕ} : (m * n) mod m = 0 :=
!mul.comm ▸ mod_mul_self_right

-- add_rewrite mod_mul_self_left

-- ### properties of div and mod together

theorem mod_lt {x y : ℕ} (H : y > 0) : x mod y < y :=
case_strong_induction_on x
  (show 0 mod y < y, from !zero_mod⁻¹ ▸ H)
  (take x,
    assume IH : ∀x', x' ≤ x → x' mod y < y,
    show succ x mod y < y, from
      by_cases -- (succ x < y)
        (assume H1 : succ x < y,
          have H2 : succ x mod y = succ x, from mod_less H1,
          show succ x mod y < y, from H2⁻¹ ▸ H1)
        (assume H1 : ¬ succ x < y,
          have H2 : y ≤ succ x, from not_lt_imp_ge H1,
          have H3 : succ x mod y = (succ x - y) mod y, from mod_rec H H2,
          have H4 : succ x - y < succ x, from sub_lt !succ_pos H,
          have H5 : succ x - y ≤ x, from lt_succ_imp_le H4,
          show succ x mod y < y, from H3⁻¹ ▸ IH _ H5))

theorem div_mod_eq {x y : ℕ} : x = x div y * y + x mod y :=
case_zero_pos y
  (show x = x div 0 * 0 + x mod 0, from
    (calc
      x div 0 * 0 + x mod 0 = 0 + x mod 0 : {!mul.zero_right}
        ... = x mod 0 : !add.zero_left
        ... = x : mod_zero)⁻¹)
  (take y,
    assume H : y > 0,
    show x = x div y * y + x mod y, from
      case_strong_induction_on x
        (show 0 = (0 div y) * y + 0 mod y, by simp)
        (take x,
          assume IH : ∀x', x' ≤ x → x' = x' div y * y + x' mod y,
          show succ x = succ x div y * y + succ x mod y, from
            by_cases -- (succ x < y)
              (assume H1 : succ x < y,
                have H2 : succ x div y = 0, from div_less H1,
                have H3 : succ x mod y = succ x, from mod_less H1,
                by simp)
              (assume H1 : ¬ succ x < y,
                have H2 : y ≤ succ x, from not_lt_imp_ge H1,
                have H3 : succ x div y = succ ((succ x - y) div y), from div_rec H H2,
                have H4 : succ x mod y = (succ x - y) mod y, from mod_rec H H2,
                have H5 : succ x - y < succ x, from sub_lt !succ_pos H,
                have H6 : succ x - y ≤ x, from lt_succ_imp_le H5,
                (calc
                  succ x div y * y + succ x mod y = succ ((succ x - y) div y) * y + succ x mod y :
                      {H3}
                    ... = ((succ x - y) div y) * y + y + succ x mod y : {!mul.succ_left}
                    ... = ((succ x - y) div y) * y + y + (succ x - y) mod y : {H4}
                    ... = ((succ x - y) div y) * y + (succ x - y) mod y + y : !add.right_comm
                    ... = succ x - y + y : {(IH _ H6)⁻¹}
                    ... = succ x : add_sub_ge_left H2)⁻¹)))

theorem mod_le {x y : ℕ} : x mod y ≤ x :=
div_mod_eq⁻¹ ▸ !le_add_left

--- a good example where simplifying using the context causes problems
theorem remainder_unique {y : ℕ} (H : y > 0) {q1 r1 q2 r2 : ℕ} (H1 : r1 < y) (H2 : r2 < y)
  (H3 : q1 * y + r1 = q2 * y + r2) : r1 = r2 :=
calc
  r1 = r1 mod y : by simp
    ... = (r1 + q1 * y) mod y : (mod_add_mul_self_right H)⁻¹
    ... = (q1 * y + r1) mod y : {!add.comm}
    ... = (r2 + q2 * y) mod y : by simp
    ... = r2 mod y            : mod_add_mul_self_right H
    ... = r2                  : by simp

theorem quotient_unique {y : ℕ} (H : y > 0) {q1 r1 q2 r2 : ℕ} (H1 : r1 < y) (H2 : r2 < y)
  (H3 : q1 * y + r1 = q2 * y + r2) : q1 = q2 :=
have H4 : q1 * y + r2 = q2 * y + r2, from (remainder_unique H H1 H2 H3) ▸ H3,
have H5 : q1 * y = q2 * y, from add.cancel_right H4,
have H6 : y > 0, from le_lt.trans !zero_le H1,
show q1 = q2, from mul_cancel_right H6 H5

theorem div_mul_mul {z x y : ℕ} (zpos : z > 0) : (z * x) div (z * y) = x div y :=
by_cases -- (y = 0)
  (assume H : y = 0, by simp)
  (assume H : y ≠ 0,
    have ypos : y > 0, from ne_zero_imp_pos H,
    have zypos : z * y > 0, from mul_pos zpos ypos,
    have H1 : (z * x) mod (z * y) < z * y, from mod_lt zypos,
    have H2 : z * (x mod y) < z * y, from mul_lt_left zpos (mod_lt ypos),
    quotient_unique zypos H1 H2
      (calc
        ((z * x) div (z * y)) * (z * y) + (z * x) mod (z * y) = z * x : div_mod_eq⁻¹
          ... = z * (x div y * y + x mod y)                           : {div_mod_eq}
          ... = z * (x div y * y) + z * (x mod y)                     : !mul.distr_left
          ... = (x div y) * (z * y) + z * (x mod y)                   : {!mul.left_comm}))
--- something wrong with the term order
---            ... = (x div y) * (z * y) + z * (x mod y) : by simp))

theorem mod_mul_mul {z x y : ℕ} (zpos : z > 0) : (z * x) mod (z * y) = z * (x mod y) :=
by_cases -- (y = 0)
  (assume H : y = 0, by simp)
  (assume H : y ≠ 0,
    have ypos : y > 0, from ne_zero_imp_pos H,
    have zypos : z * y > 0, from mul_pos zpos ypos,
    have H1 : (z * x) mod (z * y) < z * y, from mod_lt zypos,
    have H2 : z * (x mod y) < z * y, from mul_lt_left zpos (mod_lt ypos),
    remainder_unique zypos H1 H2
      (calc
        ((z * x) div (z * y)) * (z * y) + (z * x) mod (z * y) = z * x : div_mod_eq⁻¹
          ... = z * (x div y * y + x mod y) : {div_mod_eq}
          ... = z * (x div y * y) + z * (x mod y) : !mul.distr_left
          ... = (x div y) * (z * y) + z * (x mod y) : {!mul.left_comm}))

theorem mod_one {x : ℕ} : x mod 1 = 0 :=
have H1 : x mod 1 < 1, from mod_lt !succ_pos,
le_zero (lt_succ_imp_le H1)

-- add_rewrite mod_one

theorem mod_self {n : ℕ} : n mod n = 0 :=
case n (by simp)
  (take n,
    have H : (succ n * 1) mod (succ n * 1) = succ n * (1 mod 1),
      from mod_mul_mul !succ_pos,
    (by simp) ▸ H)

-- add_rewrite mod_self

theorem div_one {n : ℕ} : n div 1 = n :=
have H : n div 1 * 1 + n mod 1 = n, from div_mod_eq⁻¹,
(by simp) ▸ H

-- add_rewrite div_one

theorem pos_div_self {n : ℕ} (H : n > 0) : n div n = 1 :=
have H1 : (n * 1) div (n * 1) = 1 div 1, from div_mul_mul H,
(by simp) ▸ H1

-- add_rewrite pos_div_self

-- Divides
-- -------
definition dvd (x y : ℕ) : Prop := y mod x = 0

infix `|` := dvd

theorem dvd_iff_mod_eq_zero {x y : ℕ} : x | y ↔ y mod x = 0 :=
eq_to_iff rfl

theorem dvd_imp_div_mul_eq {x y : ℕ} (H : y | x) : x div y * y = x :=
(calc
  x = x div y * y + x mod y : div_mod_eq
    ... = x div y * y + 0 : {mp dvd_iff_mod_eq_zero H}
    ... = x div y * y : !add.zero_right)⁻¹

-- add_rewrite dvd_imp_div_mul_eq

theorem mul_eq_imp_dvd {z x y : ℕ} (H : z * y = x) :  y | x :=
have H1 : z * y = x mod y + x div y * y, from
  H ⬝ div_mod_eq ⬝ !add.comm,
have H2 : (z - x div y) * y = x mod y, from
  calc
    (z - x div y) * y = z * y - x div y * y      : !mul_sub_distr_right
       ... = x mod y + x div y * y - x div y * y : {H1}
       ... = x mod y                             : !sub_add_left,
show x mod y = 0, from
  by_cases
    (assume yz : y = 0,
      have xz : x = 0, from
        calc
          x = z * y     : H⁻¹
            ... = z * 0 : {yz}
            ... = 0     : !mul.zero_right,
      calc
        x mod y = x mod 0 : {yz}
          ... = x         : mod_zero
          ... = 0         : xz)
    (assume ynz : y ≠ 0,
      have ypos : y > 0, from ne_zero_imp_pos ynz,
      have H3 : (z - x div y) * y < y, from H2⁻¹ ▸ mod_lt ypos,
      have H4 : (z - x div y) * y < 1 * y, from !mul.one_left⁻¹ ▸ H3,
      have H5 : z - x div y < 1, from mul_lt_cancel_right H4,
      have H6 : z - x div y = 0, from le_zero (lt_succ_imp_le H5),
      calc
        x mod y = (z - x div y) * y : H2⁻¹
            ... = 0 * y : {H6}
            ... = 0 : !mul.zero_left)

theorem dvd_iff_exists_mul {x y : ℕ} : x | y ↔ ∃z, z * x = y :=
iff.intro
  (assume H : x | y,
    show ∃z, z * x = y, from exists_intro _ (dvd_imp_div_mul_eq H))
  (assume H : ∃z, z * x = y,
    obtain (z : ℕ) (zx_eq : z * x = y), from H,
    show x | y, from mul_eq_imp_dvd zx_eq)

theorem dvd_zero {n : ℕ} : n | 0 := sorry
-- (by simp) (dvd_iff_mod_eq_zero n 0)

-- add_rewrite dvd_zero

theorem zero_dvd_iff {n : ℕ} : (0 | n) = (n = 0) := sorry
-- (by simp) (dvd_iff_mod_eq_zero 0 n)

-- add_rewrite zero_dvd_iff

theorem one_dvd {n : ℕ} : 1 | n := sorry
-- (by simp) (dvd_iff_mod_eq_zero 1 n)

-- add_rewrite one_dvd

theorem dvd_self {n : ℕ} : n | n := sorry
-- (by simp) (dvd_iff_mod_eq_zero n n)

-- add_rewrite dvd_self

theorem dvd_mul_self_left {m n : ℕ} : m | (m * n) := sorry
-- (by simp) (dvd_iff_mod_eq_zero m (m * n))

-- add_rewrite dvd_mul_self_left

theorem dvd_mul_self_right {m n : ℕ} : m | (n * m) := sorry
-- (by simp) (dvd_iff_mod_eq_zero m (n * m))

-- add_rewrite dvd_mul_self_left

theorem dvd_trans {m n k : ℕ} (H1 : m | n) (H2 : n | k) : m | k :=
have H3 : n = n div m * m, by simp,
have H4 : k = k div n * (n div m) * m, from
  calc
    k = k div n * n : by simp
      ... = k div n * (n div m * m) : {H3}
      ... = k div n * (n div m) * m : !mul.assoc⁻¹,
mp (dvd_iff_exists_mul⁻¹) (exists_intro (k div n * (n div m)) (H4⁻¹))

theorem dvd_add {m n1 n2 : ℕ} (H1 : m | n1) (H2 : m | n2) : m | (n1 + n2) :=
have H : (n1 div m + n2 div m) * m = n1 + n2, by simp,
mp (dvd_iff_exists_mul⁻¹) (exists_intro _ H)

theorem dvd_add_cancel_left {m n1 n2 : ℕ} : m | (n1 + n2) → m | n1 → m | n2 :=
case_zero_pos m
  (assume H1 : 0 | n1 + n2,
    assume H2 : 0 | n1,
    have H3 : n1 + n2 = 0, from zero_dvd_iff ▸ H1,
    have H4 : n1 = 0, from zero_dvd_iff ▸ H2,
    have H5 : n2 = 0, from mp (by simp) (H4 ▸ H3),
    show 0 | n2, by simp)
  (take m,
    assume mpos : m > 0,
    assume H1 : m | (n1 + n2),
    assume H2 : m | n1,
    have H3 : n1 + n2 = n1 + n2 div m * m, from
     calc
       n1 + n2 = (n1 + n2) div m * m : by simp
         ... = (n1 div m * m + n2) div m * m : by simp
         ... = (n2 + n1 div m * m) div m * m : {!add.comm}
         ... = (n2 div m + n1 div m) * m     : {div_add_mul_self_right mpos}
         ... = n2 div m * m + n1 div m * m   : !mul.distr_right
         ... = n1 div m * m + n2 div m * m   : !add.comm
         ... = n1 + n2 div m * m : by simp,
    have H4 : n2 = n2 div m * m, from add.cancel_left H3,
    mp (dvd_iff_exists_mul⁻¹) (exists_intro _ (H4⁻¹)))

theorem dvd_add_cancel_right {m n1 n2 : ℕ} (H : m | (n1 + n2)) : m | n2 → m | n1 :=
dvd_add_cancel_left (!add.comm ▸ H)

theorem dvd_sub {m n1 n2 : ℕ} (H1 : m | n1) (H2 : m | n2) : m | (n1 - n2) :=
by_cases
  (assume H3 : n1 ≥ n2,
    have H4 : n1 = n1 - n2 + n2, from (add_sub_ge_left H3)⁻¹,
    show m | n1 - n2, from dvd_add_cancel_right (H4 ▸ H1) H2)
  (assume H3 : ¬ (n1 ≥ n2),
    have H4 : n1 - n2 = 0, from le_imp_sub_eq_zero (lt_imp_le (not_le_imp_gt H3)),
    show m | n1 - n2, from H4⁻¹ ▸ dvd_zero)

-- Gcd and lcm
-- -----------

definition pair_nat.lt    := lex lt lt
definition pair_nat.lt.wf [instance] : well_founded pair_nat.lt :=
prod.lex.wf lt.wf lt.wf
infixl `≺`:50 := pair_nat.lt

-- Lemma for justifying recursive call
private definition gcd.lt1 (x₁ y₁ : nat) : (x₁ - y₁, succ y₁) ≺ (succ x₁, succ y₁) :=
!lex.left (le_imp_lt_succ (sub_le_self x₁ y₁))

-- Lemma for justifying recursive call
private definition gcd.lt2 (x₁ y₁ : nat) : (succ x₁, y₁ - x₁) ≺ (succ x₁, succ y₁) :=
!lex.right (le_imp_lt_succ (sub_le_self y₁ x₁))

private definition gcd.F (p₁ : nat × nat) : (Π p₂ : nat × nat, p₂ ≺ p₁ → nat) → nat :=
prod.cases_on p₁ (λ (x y : nat),
nat.cases_on x
  (λ f, y) -- x = 0
  (λ x₁, nat.cases_on y
     (λ f, succ x₁) -- y = 0
     (λ y₁ (f : (Π p₂ : nat × nat, p₂ ≺ (succ x₁, succ y₁) → nat)),
        if y₁ ≤ x₁ then f (x₁ - y₁, succ y₁) !gcd.lt1
                   else f (succ x₁, y₁ - x₁) !gcd.lt2)))

definition gcd (x y : nat) :=
fix gcd.F (pair x y)

example : gcd 15 6 = 3 :=
rfl

theorem gcd_zero_left (y : nat) : gcd 0 y = y :=
well_founded.fix_eq gcd.F (0, y)

theorem gcd_succ_zero (x : nat) : gcd (succ x) 0 = succ x :=
well_founded.fix_eq gcd.F (succ x, 0)

theorem gcd_zero (x : nat) : gcd x 0 = x :=
cases_on x
  (gcd_zero_left 0)
  (λ x₁, !gcd_succ_zero)

theorem gcd_succ_succ (x y : nat) : gcd (succ x) (succ y) = if y ≤ x then gcd (x-y) (succ y) else gcd (succ x) (y-x) :=
well_founded.fix_eq gcd.F (succ x, succ y)

theorem gcd_one (n : ℕ) : gcd n 1 = 1 :=
induction_on n
  !gcd_zero_left
  (λ n₁ ih, calc gcd (succ n₁) 1
        = if 0 ≤ n₁ then gcd (n₁ - 0) 1 else gcd (succ n₁) (0 - n₁) : gcd_succ_succ
    ... = gcd (n₁ - 0) 1 : if_pos (zero_le n₁)
    ... = gcd n₁ 1       : rfl
    ... = 1              : ih)

theorem gcd_self (n : ℕ) : gcd n n = n :=
induction_on n
  !gcd_zero_left
  (λ n₁ ih, calc gcd (succ n₁) (succ n₁)
       = if n₁ ≤ n₁ then gcd (n₁-n₁) (succ n₁) else gcd (succ n₁) (n₁-n₁) : gcd_succ_succ
   ... = gcd (n₁-n₁) (succ n₁) : if_pos (le.refl n₁)
   ... = gcd 0 (succ n₁)       : sub_self
   ... = succ n₁               : gcd_zero_left)

theorem gcd_left {m n : ℕ} (H  : m < n) : gcd (succ m) (succ n) = gcd (succ m) (n - m) :=
gcd_succ_succ m n ⬝ if_neg (lt_imp_not_ge H)

theorem gcd_right {m n : ℕ} (H : n < m) : gcd (succ m) (succ n) = gcd (m - n) (succ n) :=
gcd_succ_succ m n ⬝ if_pos (le.of_lt H)

private definition gcd_dvd_prop (m n : ℕ) : Prop :=
(gcd m n | m) ∧ (gcd m n | n)

private lemma gcd_arith_eq {m n : ℕ} (h : m > n) : m - n + succ n = succ m :=
calc m - n + succ n = succ (m - n + n) : rfl
                ... = succ m           : @add_sub_ge_left m n (le.of_lt h)

private lemma gcd_dvd.F (p₁ : nat × nat) : (∀p₂, p₂ ≺ p₁ → gcd_dvd_prop (pr₁ p₂) (pr₂ p₂)) → gcd_dvd_prop (pr₁ p₁) (pr₂ p₁) :=
prod.cases_on p₁ (λ m n, cases_on m
  (λ ih, and.intro !dvd_zero (!gcd_zero_left⁻¹ ▸ !dvd_self))
  (λ m₁, cases_on n
    (λ ih, and.intro (!gcd_zero⁻¹ ▸ !dvd_self) !dvd_zero)
    (λ n₁ (ih_core : ∀p₂, p₂ ≺ (succ m₁, succ n₁) → gcd_dvd_prop (pr₁ p₂) (pr₂ p₂)),
      have ih : ∀{m₂ n₂}, (m₂, n₂) ≺ (succ m₁, succ n₁) → gcd m₂ n₂ | m₂ ∧ gcd m₂ n₂ | n₂, from
        λ m₂ n₂ hlt, ih_core (m₂, n₂) hlt,
      show (gcd (succ m₁) (succ n₁) | (succ m₁)) ∧ (gcd (succ m₁) (succ n₁) | (succ n₁)), from
      or.elim (trichotomy n₁ m₁)
        (λ hlt : n₁ < m₁,
          have aux₁ : gcd (succ m₁) (succ n₁) = gcd (m₁ - n₁) (succ n₁), from gcd_right hlt,
          have aux₂ : gcd (m₁ - n₁) (succ n₁) | (m₁ - n₁),   from and.elim_left  (ih !gcd.lt1),
          have aux₃ : gcd (m₁ - n₁) (succ n₁) | succ n₁,     from and.elim_right (ih !gcd.lt1),
          have aux₄ : gcd (m₁ - n₁) (succ n₁) | succ m₁,     from gcd_arith_eq hlt ▸ dvd_add aux₂ aux₃,
          and.intro (aux₁⁻¹ ▸ aux₄) (aux₁⁻¹ ▸ aux₃))
        (λ h, or.elim h
        (λ heq : n₁ = m₁,
           have aux : gcd (succ n₁) (succ n₁) | (succ n₁), from gcd_self (succ n₁) ▸ !dvd_self,
           eq.rec_on heq (and.intro aux aux))
        (λ hgt : n₁ > m₁,
          have aux₁ : gcd (succ m₁) (succ n₁) = gcd (succ m₁) (n₁ - m₁), from gcd_left hgt,
          have aux₂ : gcd (succ m₁) (n₁ - m₁) | succ m₁,   from and.elim_left  (ih !gcd.lt2),
          have aux₃ : gcd (succ m₁) (n₁ - m₁) | (n₁ - m₁), from and.elim_right (ih !gcd.lt2),
          have aux₄ : gcd (succ m₁) (n₁ - m₁) | succ n₁,   from gcd_arith_eq hgt ▸ dvd_add aux₃ aux₂,
          and.intro (aux₁⁻¹ ▸ aux₂) (aux₁⁻¹ ▸ aux₄))))))

theorem gcd_dvd (m n : ℕ) : (gcd m n | m) ∧ (gcd m n | n) :=
well_founded.induction (m, n) gcd_dvd.F

theorem gcd_dvd_left (m n : ℕ) : (gcd m n | m) := and.elim_left !gcd_dvd

theorem gcd_dvd_right (m n : ℕ) : (gcd m n | n) := and.elim_right !gcd_dvd

theorem gcd_greatest {m n k : ℕ} : k | m → k | n → k | (gcd m n) :=
sorry

end nat

/-
theorem gcd_pos (m : ℕ) {n : ℕ} (H : n > 0) : gcd m n = gcd n (m mod n) :=
gcd_def m n ⬝ if_neg (pos_imp_ne_zero H)

theorem gcd_zero_left (x : ℕ) : gcd 0 x = x :=
case x (by simp) (take x, (gcd_def _ _) ⬝ (by simp))

-- add_rewrite gcd_zero_left

theorem gcd_induct {P : ℕ → ℕ → Prop} (m n : ℕ) (H0 : ∀m, P m 0)
  (H1 : ∀m n, 0 < n → P n (m mod n) → P m n) : P m n :=
have aux : ∀m, P m n, from
  case_strong_induction_on n H0
    (take n,
      assume IH : ∀k, k ≤ n → ∀m, P m k,
      take m,
      have H2 : m mod succ n ≤ n, from lt_succ_imp_le (mod_lt !succ_pos),
      have H3 : P (succ n) (m mod succ n), from IH _ H2 _,
      show P m (succ n), from H1 _ _ !succ_pos H3),
aux m

theorem gcd_succ (m n : ℕ) : gcd m (succ n) = gcd (succ n) (m mod succ n) :=
!gcd_def ⬝ if_neg !succ_ne_zero

theorem gcd_greatest {m n k : ℕ} : k | m → k | n → k | (gcd m n) :=
gcd_induct m n
  (take m, assume H : k | m, sorry) -- by simp)
  (take m n,
    assume npos : n > 0,
    assume IH : k | n → k | (m mod n) → k | gcd n (m mod n),
    assume H1 : k | m,
    assume H2 : k | n,
    have H3 : k | m div n * n + m mod n, from div_mod_eq ▸ H1,
    have H4 : k | m mod n, from dvd_add_cancel_left H3 (dvd_trans H2 (by simp)),
    have gcd_eq : gcd n (m mod n) = gcd m n, from (gcd_pos _ npos)⁻¹,
    show k | gcd m n, from gcd_eq ▸ IH H2 H4)
-/
