/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

Definitions and properties of div and mod. Much of the development follows Isabelle's library.
-/
import data.nat.sub
open eq.ops well_founded decidable prod

namespace nat

/- div -/

-- auxiliary lemma used to justify div
private definition div_rec_lemma {x y : nat} : 0 < y ∧ y ≤ x → x - y < x :=
and.rec (λ ypos ylex, sub_lt (lt_of_lt_of_le ypos ylex) ypos)

private definition div.F (x : nat) (f : Π x₁, x₁ < x → nat → nat) (y : nat) : nat :=
if H : 0 < y ∧ y ≤ x then f (x - y) (div_rec_lemma H) y + 1 else zero

definition divide := fix div.F
notation a div b := divide a b

theorem divide_def (x y : nat) : divide x y = if 0 < y ∧ y ≤ x then divide (x - y) y + 1 else 0 :=
congr_fun (fix_eq div.F x) y

theorem div_zero (a : ℕ) : a div 0 = 0 :=
divide_def a 0 ⬝ if_neg (!not_and_of_not_left (lt.irrefl 0))

theorem div_eq_zero_of_lt {a b : ℕ} (h : a < b) : a div b = 0 :=
divide_def a b ⬝ if_neg (!not_and_of_not_right (not_le_of_gt h))

theorem zero_div (b : ℕ) : 0 div b = 0 :=
divide_def 0 b ⬝ if_neg (and.rec not_le_of_gt)

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
      (x + succ y * z) div z = (x + (y * z + z)) div z  : succ_mul
                         ... = (x + y * z + z) div z    : add.assoc
                         ... = succ ((x + y * z) div z) : !add_div_self H
                         ... = succ (x div z + y)       : IH)

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

/- mod -/

private definition mod.F (x : nat) (f : Π x₁, x₁ < x → nat → nat) (y : nat) : nat :=
if H : 0 < y ∧ y ≤ x then f (x - y) (div_rec_lemma H) y else x

definition modulo := fix mod.F
notation a mod b := modulo a b
notation a `≡` b `[mod`:100 c `]`:0 := a mod c = b mod c

theorem modulo_def (x y : nat) : modulo x y = if 0 < y ∧ y ≤ x then modulo (x - y) y else x :=
congr_fun (fix_eq mod.F x) y

theorem mod_zero (a : ℕ) : a mod 0 = a :=
modulo_def a 0 ⬝ if_neg (!not_and_of_not_left (lt.irrefl 0))

theorem mod_eq_of_lt {a b : ℕ} (h : a < b) : a mod b = a :=
modulo_def a b ⬝ if_neg (!not_and_of_not_right (not_le_of_gt h))

theorem zero_mod (b : ℕ) : 0 mod b = 0 :=
modulo_def 0 b ⬝ if_neg (λ h, and.rec_on h (λ l r, absurd (lt_of_lt_of_le l r) (lt.irrefl 0)))

theorem mod_eq_sub_mod {a b : ℕ} (h₁ : b > 0) (h₂ : a ≥ b) : a mod b = (a - b) mod b :=
modulo_def a b ⬝ if_pos (and.intro h₁ h₂)

theorem add_mod_self (x z : ℕ) : (x + z) mod z = x mod z :=
by_cases_zero_pos z
  (by rewrite add_zero)
  (take z, assume H : z > 0,
    calc
      (x + z) mod z = if 0 < z ∧ z ≤ x + z then (x + z - z) mod z else _ : modulo_def
                ... = (x + z - z) mod z   : if_pos (and.intro H (le_add_left z x))
                ... = x mod z             : add_sub_cancel)

theorem add_mod_self_left (x z : ℕ) : (x + z) mod x = z mod x :=
!add.comm ▸ !add_mod_self

theorem add_mul_mod_self (x y z : ℕ) : (x + y * z) mod z = x mod z :=
nat.induction_on y
  (calc (x + zero * z) mod z = (x + zero) mod z : zero_mul
                         ... = x mod z          : add_zero)
  (take y,
    assume IH : (x + y * z) mod z = x mod z,
    calc
      (x + succ y * z) mod z = (x + (y * z + z)) mod z : succ_mul
                         ... = (x + y * z + z) mod z   : add.assoc
                         ... = (x + y * z) mod z       : !add_mod_self
                         ... = x mod z                 : IH)

theorem add_mul_mod_self_left (x y z : ℕ) : (x + y * z) mod y = x mod y :=
!mul.comm ▸ !add_mul_mod_self

theorem mul_mod_left (m n : ℕ) : (m * n) mod n = 0 :=
by rewrite [-zero_add (m * n), add_mul_mod_self, zero_mod]

theorem mul_mod_right (m n : ℕ) : (m * n) mod m = 0 :=
!mul.comm ▸ !mul_mod_left

theorem mod_lt (x : ℕ) {y : ℕ} (H : y > 0) : x mod y < y :=
nat.case_strong_induction_on x
  (show 0 mod y < y, from !zero_mod⁻¹ ▸ H)
  (take x,
    assume IH : ∀x', x' ≤ x → x' mod y < y,
    show succ x mod y < y, from
      by_cases -- (succ x < y)
        (assume H1 : succ x < y,
          have succ x mod y = succ x, from mod_eq_of_lt H1,
          show succ x mod y < y, from this⁻¹ ▸ H1)
        (assume H1 : ¬ succ x < y,
          have y ≤ succ x, from le_of_not_gt H1,
          have h : succ x mod y = (succ x - y) mod y, from mod_eq_sub_mod H this,
          have succ x - y < succ x, from sub_lt !succ_pos H,
          have succ x - y ≤ x, from le_of_lt_succ this,
          show succ x mod y < y, from h⁻¹ ▸ IH _ this))

theorem mod_one (n : ℕ) : n mod 1 = 0 :=
have H1 : n mod 1 < 1, from !mod_lt !succ_pos,
eq_zero_of_le_zero (le_of_lt_succ H1)

/- properties of div and mod -/

-- the quotient / remainder theorem
theorem eq_div_mul_add_mod (x y : ℕ) : x = x div y * y + x mod y :=
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
        (show 0 = (0 div y) * y + 0 mod y, by rewrite [zero_mod, add_zero, zero_div, zero_mul])
        (take x,
          assume IH : ∀x', x' ≤ x → x' = x' div y * y + x' mod y,
          show succ x = succ x div y * y + succ x mod y, from
            if H1 : succ x < y then
                have H2 : succ x div y = 0, from div_eq_zero_of_lt H1,
                have H3 : succ x mod y = succ x, from mod_eq_of_lt H1,
                H2⁻¹ ▸ H3⁻¹ ▸ !zero_mul⁻¹ ▸ !zero_add⁻¹
            else
                have H2 : y ≤ succ x, from le_of_not_gt H1,
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
                    ... = succ x                                         : sub_add_cancel H2)⁻¹))

theorem mod_eq_sub_div_mul (x y : ℕ) : x mod y = x - x div y * y :=
eq_sub_of_add_eq (!add.comm ▸ !eq_div_mul_add_mod)⁻¹

theorem mod_add_mod (m n k : ℕ) : (m mod n + k) mod n = (m + k) mod n :=
by rewrite [eq_div_mul_add_mod m n at {2}, add.assoc, add.comm (m div n * n), add_mul_mod_self]

theorem add_mod_mod (m n k : ℕ) : (m + n mod k) mod k = (m + n) mod k :=
by rewrite [add.comm, mod_add_mod, add.comm]

theorem add_mod_eq_add_mod_right {m n k : ℕ} (i : ℕ) (H : m mod n = k mod n) :
  (m + i) mod n = (k + i) mod n :=
by rewrite [-mod_add_mod, -mod_add_mod k, H]

theorem add_mod_eq_add_mod_left {m n k : ℕ} (i : ℕ) (H : m mod n = k mod n) :
  (i + m) mod n = (i + k) mod n :=
by rewrite [add.comm, add_mod_eq_add_mod_right _ H, add.comm]

theorem mod_eq_mod_of_add_mod_eq_add_mod_right {m n k i : ℕ} :
  (m + i) mod n = (k + i) mod n → m mod n = k mod n :=
by_cases_zero_pos n
  (by rewrite [*mod_zero]; apply eq_of_add_eq_add_right)
  (take n,
    assume npos : n > 0,
    assume H1 : (m + i) mod n = (k + i) mod n,
    have H2 : (m + i mod n) mod n = (k + i mod n) mod n, by rewrite [*add_mod_mod, H1],
    assert H3 : (m + i mod n + (n - i mod n)) mod n = (k + i mod n + (n - i mod n)) mod n,
      from add_mod_eq_add_mod_right _ H2,
    begin
      revert H3,
      rewrite [*add.assoc, add_sub_of_le (le_of_lt (!mod_lt npos)), *add_mod_self],
      intros, assumption
    end)

theorem mod_eq_mod_of_add_mod_eq_add_mod_left {m n k i : ℕ} :
  (i + m) mod n = (i + k) mod n → m mod n = k mod n :=
by rewrite [add.comm i m, add.comm i k]; apply mod_eq_mod_of_add_mod_eq_add_mod_right

theorem mod_le {x y : ℕ} : x mod y ≤ x :=
!eq_div_mul_add_mod⁻¹ ▸ !le_add_left

theorem eq_remainder {q1 r1 q2 r2 y : ℕ} (H1 : r1 < y) (H2 : r2 < y)
  (H3 : q1 * y + r1 = q2 * y + r2) : r1 = r2 :=
calc
  r1 = r1 mod y               : mod_eq_of_lt H1
    ... = (r1 + q1 * y) mod y : !add_mul_mod_self⁻¹
    ... = (q1 * y + r1) mod y : add.comm
    ... = (r2 + q2 * y) mod y : by rewrite [H3, add.comm]
    ... = r2 mod y            : !add_mul_mod_self
    ... = r2                  : mod_eq_of_lt H2

theorem eq_quotient {q1 r1 q2 r2 y : ℕ} (H1 : r1 < y) (H2 : r2 < y)
  (H3 : q1 * y + r1 = q2 * y + r2) : q1 = q2 :=
have H4 : q1 * y + r2 = q2 * y + r2, from (eq_remainder H1 H2 H3) ▸ H3,
have H5 : q1 * y = q2 * y, from add.cancel_right H4,
have H6 : y > 0, from lt_of_le_of_lt !zero_le H1,
show q1 = q2, from eq_of_mul_eq_mul_right H6 H5

theorem mul_div_mul_left {z : ℕ} (x y : ℕ) (zpos : z > 0) : (z * x) div (z * y) = x div y :=
if H : y = 0 then H⁻¹ ▸ !mul_zero⁻¹ ▸ !div_zero⁻¹ ▸ !div_zero
else
    have ypos : y > 0, from pos_of_ne_zero H,
    have zypos : z * y > 0, from mul_pos zpos ypos,
    have H1 : (z * x) mod (z * y) < z * y, from !mod_lt zypos,
    have H2 : z * (x mod y) < z * y, from mul_lt_mul_of_pos_left (!mod_lt ypos) zpos,
    eq_quotient H1 H2
      (calc
        ((z * x) div (z * y)) * (z * y) + (z * x) mod (z * y) = z * x : eq_div_mul_add_mod
          ... = z * (x div y * y + x mod y)                           : eq_div_mul_add_mod
          ... = z * (x div y * y) + z * (x mod y)                     : mul.left_distrib
          ... = (x div y) * (z * y) + z * (x mod y)                   : mul.left_comm)

theorem mul_div_mul_right {x z y : ℕ} (zpos : z > 0) : (x * z) div (y * z) = x div y :=
!mul.comm ▸ !mul.comm ▸ !mul_div_mul_left zpos

theorem mul_mod_mul_left (z x y : ℕ) : (z * x) mod (z * y) = z * (x mod y) :=
or.elim (eq_zero_or_pos z)
  (assume H : z = 0, H⁻¹ ▸ calc
      (0 * x) mod (z * y) = 0 mod (z * y)       : zero_mul
                      ... = 0                   : zero_mod
                      ... = 0 * (x mod y)       : zero_mul)
  (assume zpos : z > 0,
    or.elim (eq_zero_or_pos y)
      (assume H : y = 0, by rewrite [H, mul_zero, *mod_zero])
      (assume ypos : y > 0,
        have zypos : z * y > 0, from mul_pos zpos ypos,
        have H1 : (z * x) mod (z * y) < z * y, from !mod_lt zypos,
        have H2 : z * (x mod y) < z * y, from mul_lt_mul_of_pos_left (!mod_lt ypos) zpos,
        eq_remainder H1 H2
          (calc
            ((z * x) div (z * y)) * (z * y) + (z * x) mod (z * y) = z * x : eq_div_mul_add_mod
              ... = z * (x div y * y + x mod y)                           : eq_div_mul_add_mod
              ... = z * (x div y * y) + z * (x mod y)                     : mul.left_distrib
              ... = (x div y) * (z * y) + z * (x mod y)                   : mul.left_comm)))

theorem mul_mod_mul_right (x z y : ℕ) : (x * z) mod (y * z) = (x mod y) * z :=
mul.comm z x ▸ mul.comm z y ▸ !mul.comm ▸ !mul_mod_mul_left

theorem mod_self (n : ℕ) : n mod n = 0 :=
nat.cases_on n (by rewrite zero_mod)
  (take n, by rewrite [-zero_add (succ n) at {1}, add_mod_self])

theorem mul_mod_eq_mod_mul_mod (m n k : nat) : (m * n) mod k = ((m mod k) * n) mod k :=
calc
  (m * n) mod k = (((m div k) * k + m mod k) * n) mod k : eq_div_mul_add_mod
            ... = ((m mod k) * n) mod k                 :
                    by rewrite [mul.right_distrib, mul.right_comm, add.comm, add_mul_mod_self]

theorem mul_mod_eq_mul_mod_mod (m n k : nat) : (m * n) mod k = (m * (n mod k)) mod k :=
!mul.comm ▸ !mul.comm ▸ !mul_mod_eq_mod_mul_mod

theorem div_one (n : ℕ) : n div 1 = n :=
assert n div 1 * 1 + n mod 1 = n, from !eq_div_mul_add_mod⁻¹,
begin rewrite [-this at {2}, mul_one, mod_one] end

theorem div_self {n : ℕ} (H : n > 0) : n div n = 1 :=
assert (n * 1) div (n * 1) = 1 div 1, from !mul_div_mul_left H,
by rewrite [div_one at this, -this, *mul_one]

theorem div_mul_cancel_of_mod_eq_zero {m n : ℕ} (H : m mod n = 0) : m div n * n = m :=
by rewrite [eq_div_mul_add_mod m n at {2}, H, add_zero]

theorem mul_div_cancel_of_mod_eq_zero {m n : ℕ} (H : m mod n = 0) : n * (m div n) = m :=
!mul.comm ▸ div_mul_cancel_of_mod_eq_zero H

/- dvd -/

theorem dvd_of_mod_eq_zero {m n : ℕ} (H : n mod m = 0) : m ∣ n :=
dvd.intro (!mul.comm ▸ div_mul_cancel_of_mod_eq_zero H)

theorem mod_eq_zero_of_dvd {m n : ℕ} (H : m ∣ n) : n mod m = 0 :=
dvd.elim H (take z, assume H1 : n = m * z, H1⁻¹ ▸ !mul_mod_right)

theorem dvd_iff_mod_eq_zero (m n : ℕ) : m ∣ n ↔ n mod m = 0 :=
iff.intro mod_eq_zero_of_dvd dvd_of_mod_eq_zero

definition dvd.decidable_rel [instance] : decidable_rel dvd :=
take m n, decidable_of_decidable_of_iff _ (iff.symm !dvd_iff_mod_eq_zero)

theorem div_mul_cancel {m n : ℕ} (H : n ∣ m) : m div n * n = m :=
div_mul_cancel_of_mod_eq_zero (mod_eq_zero_of_dvd H)

theorem mul_div_cancel' {m n : ℕ} (H : n ∣ m) : n * (m div n) = m :=
!mul.comm ▸ div_mul_cancel H

theorem dvd_of_dvd_add_left {m n₁ n₂ : ℕ} (H₁ : m ∣ n₁ + n₂) (H₂ : m ∣ n₁) : m ∣ n₂ :=
obtain (c₁ : nat) (Hc₁ : n₁ + n₂ = m * c₁), from H₁,
obtain (c₂ : nat) (Hc₂ : n₁ = m * c₂), from H₂,
have   aux : m * (c₁ - c₂) = n₂, from calc
  m * (c₁ - c₂) = m * c₁  - m * c₂ : mul_sub_left_distrib
           ...  = n₁ + n₂ - m * c₂ : Hc₁
           ...  = n₁ + n₂ - n₁     : Hc₂
           ...  = n₂               : add_sub_cancel_left,
dvd.intro aux

theorem dvd_of_dvd_add_right {m n₁ n₂ : ℕ} (H : m ∣ n₁ + n₂) : m ∣ n₂ → m ∣ n₁ :=
dvd_of_dvd_add_left (!add.comm ▸ H)

theorem dvd_sub {m n₁ n₂ : ℕ} (H1 : m ∣ n₁) (H2 : m ∣ n₂) : m ∣ n₁ - n₂ :=
by_cases
  (assume H3 : n₁ ≥ n₂,
    have H4 : n₁ = n₁ - n₂ + n₂, from (sub_add_cancel H3)⁻¹,
    show m ∣ n₁ - n₂, from dvd_of_dvd_add_right (H4 ▸ H1) H2)
  (assume H3 : ¬ (n₁ ≥ n₂),
    have H4 : n₁ - n₂ = 0, from sub_eq_zero_of_le (le_of_lt (lt_of_not_ge H3)),
    show m ∣ n₁ - n₂, from H4⁻¹ ▸ dvd_zero _)

theorem dvd.antisymm {m n : ℕ} : m ∣ n → n ∣ m → m = n :=
by_cases_zero_pos n
  (assume H1, assume H2 : 0 ∣ m, eq_zero_of_zero_dvd H2)
  (take n,
    assume Hpos : n > 0,
    assume H1 : m ∣ n,
    assume H2 : n ∣ m,
    obtain k (Hk : n = m * k), from exists_eq_mul_right_of_dvd H1,
    obtain l (Hl : m = n * l), from exists_eq_mul_right_of_dvd H2,
    have n * (l * k) = n, from !mul.assoc ▸ Hl ▸ Hk⁻¹,
    have l * k = 1,       from eq_one_of_mul_eq_self_right Hpos this,
    have k = 1,           from eq_one_of_mul_eq_one_left this,
    show m = n,           from (mul_one m)⁻¹ ⬝ (this ▸ Hk⁻¹))

theorem mul_div_assoc (m : ℕ) {n k : ℕ} (H : k ∣ n) : m * n div k = m * (n div k) :=
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

theorem dvd_of_mul_dvd_mul_left {m n k : ℕ} (kpos : k > 0) (H : k * m ∣ k * n) : m ∣ n :=
dvd.elim H
  (take l,
    assume H1 : k * n = k * m * l,
    have H2 : n = m * l, from eq_of_mul_eq_mul_left kpos (H1 ⬝ !mul.assoc),
    dvd.intro H2⁻¹)

theorem dvd_of_mul_dvd_mul_right {m n k : ℕ} (kpos : k > 0) (H : m * k ∣ n * k) : m ∣ n :=
dvd_of_mul_dvd_mul_left kpos (!mul.comm ▸ !mul.comm ▸ H)

lemma dvd_of_eq_mul (i j n : nat) : n = j*i → j ∣ n :=
begin intros, subst n, apply dvd_mul_right end

theorem div_dvd_div {k m n : ℕ} (H1 : k ∣ m) (H2 : m ∣ n) : m div k ∣ n div k :=
have H3 : m = m div k * k, from (div_mul_cancel H1)⁻¹,
have H4 : n = n div k * k, from (div_mul_cancel (dvd.trans H1 H2))⁻¹,
or.elim (eq_zero_or_pos k)
  (assume H5 : k = 0,
    have H6: n div k = 0, from (congr_arg _ H5 ⬝ !div_zero),
      H6⁻¹ ▸ !dvd_zero)
  (assume H5 : k > 0,
    dvd_of_mul_dvd_mul_right H5 (H3 ▸ H4 ▸ H2))

theorem div_eq_iff_eq_mul_right {m n : ℕ} (k : ℕ) (H : n > 0) (H' : n ∣ m) :
  m div n = k ↔ m = n * k :=
iff.intro
  (assume H1, by rewrite [-H1, mul_div_cancel' H'])
  (assume H1, by rewrite [H1, !mul_div_cancel_left H])

theorem div_eq_iff_eq_mul_left {m n : ℕ} (k : ℕ) (H : n > 0) (H' : n ∣ m) :
  m div n = k ↔ m = k * n :=
!mul.comm ▸ !div_eq_iff_eq_mul_right H H'

theorem eq_mul_of_div_eq_right {m n k : ℕ} (H1 : n ∣ m) (H2 : m div n = k) :
  m = n * k :=
calc
  m     = n * (m div n) : mul_div_cancel' H1
    ... = n * k         : H2

theorem div_eq_of_eq_mul_right {m n k : ℕ} (H1 : n > 0) (H2 : m = n * k) :
  m div n = k :=
calc
  m div n = n * k div n : H2
      ... = k           : !mul_div_cancel_left H1

theorem eq_mul_of_div_eq_left {m n k : ℕ} (H1 : n ∣ m) (H2 : m div n = k) :
  m = k * n :=
!mul.comm ▸ !eq_mul_of_div_eq_right H1 H2

theorem div_eq_of_eq_mul_left {m n k : ℕ} (H1 : n > 0) (H2 : m = k * n) :
  m div n = k :=
!div_eq_of_eq_mul_right H1 (!mul.comm ▸ H2)

lemma add_mod_eq_of_dvd (i j n : nat) : n ∣ j → (i + j) mod n = i mod n :=
assume h,
obtain k (hk : j = n * k), from exists_eq_mul_right_of_dvd h,
begin
  subst j, rewrite mul.comm,
  apply add_mul_mod_self
end

/- div and ordering -/

lemma le_of_dvd {m n} : n > 0 → m ∣ n → m ≤ n :=
assume (h₁ : n > 0) (h₂ : m ∣ n),
assert h₃ : n mod m = 0, from mod_eq_zero_of_dvd h₂,
by_contradiction
 (λ nle : ¬ m ≤ n,
   have   h₄ : m > n, from lt_of_not_ge nle,
   assert h₅ : n mod m = n, from mod_eq_of_lt h₄,
   begin
     rewrite h₃ at h₅, subst n,
     exact absurd h₁ (lt.irrefl 0)
   end)

theorem div_mul_le (m n : ℕ) : m div n * n ≤ m :=
calc
  m = m div n * n + m mod n : eq_div_mul_add_mod
    ... ≥ m div n * n       : le_add_right

theorem div_le_of_le_mul {m n k : ℕ} (H : m ≤ n * k) : m div k ≤ n :=
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
        ... ≤ n * k                       : H) H1)

theorem div_le_self (m n : ℕ) : m div n ≤ m :=
nat.cases_on n (!div_zero⁻¹ ▸ !zero_le)
  take n,
  have H : m ≤ m * succ n, from calc
        m = m * 1      : mul_one
      ... ≤ m * succ n : !mul_le_mul_left (succ_le_succ !zero_le),
  div_le_of_le_mul H

theorem mul_le_of_le_div {m n k : ℕ} (H : m ≤ n div k) : m * k ≤ n :=
calc
  m * k ≤ n div k * k : !mul_le_mul_right H
    ... ≤ n           : div_mul_le

theorem le_div_of_mul_le {m n k : ℕ} (H1 : k > 0) (H2 : m * k ≤ n) : m ≤ n div k :=
have H3 : m * k < (succ (n div k)) * k, from
  calc
    m * k ≤ n                          : H2
      ... = n div k * k + n mod k      : eq_div_mul_add_mod
      ... < n div k * k + k            : add_lt_add_left (!mod_lt H1)
      ... = (succ (n div k)) * k       : succ_mul,
le_of_lt_succ (lt_of_mul_lt_mul_right H3)

theorem le_div_iff_mul_le {m n k : ℕ} (H : k > 0) : m ≤ n div k ↔ m * k ≤ n :=
iff.intro !mul_le_of_le_div (!le_div_of_mul_le H)

theorem div_le_div {m n : ℕ} (k : ℕ) (H : m ≤ n) : m div k ≤ n div k :=
by_cases_zero_pos k
  (by rewrite [*div_zero])
  (take k, assume H1 : k > 0, le_div_of_mul_le H1 (le.trans !div_mul_le H))

theorem div_lt_of_lt_mul {m n k : ℕ} (H : m < n * k) : m div k < n :=
lt_of_mul_lt_mul_right (calc
  m div k * k ≤ m div k * k + m mod k : le_add_right
    ... = m                           : eq_div_mul_add_mod
    ... < n * k                       : H)

theorem lt_mul_of_div_lt {m n k : ℕ} (H1 : k > 0) (H2 : m div k < n) : m < n * k :=
assert H3 : succ (m div k) * k ≤ n * k, from !mul_le_mul_right (succ_le_of_lt H2),
have H4 : m div k * k + k ≤ n * k, by rewrite [succ_mul at H3]; apply H3,
calc
  m     = m div k * k + m mod k : eq_div_mul_add_mod
    ... < m div k * k + k       : add_lt_add_left (!mod_lt H1)
    ... ≤ n * k                 : H4

theorem div_lt_iff_lt_mul {m n k : ℕ} (H : k > 0) : m div k < n ↔ m < n * k :=
iff.intro (!lt_mul_of_div_lt H) !div_lt_of_lt_mul

theorem div_le_iff_le_mul_of_div {m n : ℕ} (k : ℕ) (H : n > 0) (H' : n ∣ m) :
  m div n ≤ k ↔ m ≤ k * n :=
by rewrite [propext (!le_iff_mul_le_mul_right H), !div_mul_cancel H']

theorem le_mul_of_div_le_of_div {m n k : ℕ} (H1 : n > 0) (H2 : n ∣ m) (H3 : m div n ≤ k) :
  m ≤ k * n :=
iff.mp (!div_le_iff_le_mul_of_div H1 H2) H3

-- needed for integer division
theorem mul_sub_div_of_lt {m n k : ℕ} (H : k < m * n) :
  (m * n - (k + 1)) div m = n - k div m - 1 :=
have H1 : k div m < n, from div_lt_of_lt_mul (!mul.comm ▸ H),
have H2 : n - k div m ≥ 1, from
  le_sub_of_add_le (calc
    1 + k div m = succ (k div m) : add.comm
            ... ≤ n              : succ_le_of_lt H1),
assert H3 : n - k div m = n - k div m - 1 + 1, from (sub_add_cancel H2)⁻¹,
assert H4 : m > 0, from pos_of_ne_zero (assume H': m = 0, not_lt_zero _ (!zero_mul ▸ H' ▸ H)),
have H5   : k mod m + 1 ≤ m, from succ_le_of_lt (!mod_lt H4),
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

end nat
