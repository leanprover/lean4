--- Copyright (c) 2014 Floris van Doorn. All rights reserved.
--- Released under Apache 2.0 license as described in the file LICENSE.
--- Author: Floris van Doorn

-- data.nat.sub
-- ============
--
-- Subtraction on the natural numbers, as well as min, max, and distance.

import .order
import tools.fake_simplifier

open eq.ops
open fake_simplifier

namespace nat

-- subtraction
-- -----------

theorem sub_zero_right (n : ℕ) : n - 0 = n :=
rfl

theorem sub_succ_right (n m : ℕ) : n - succ m = pred (n - m) :=
rfl

irreducible sub

theorem sub_zero_left (n : ℕ) : 0 - n = 0 :=
induction_on n !sub_zero_right
  (take k : nat,
    assume IH : 0 - k = 0,
    calc
      0 - succ k = pred (0 - k) : !sub_succ_right
             ... = pred 0       : {IH}
             ... = 0            : pred.zero)

theorem sub_succ_succ (n m : ℕ) : succ n - succ m = n - m :=
succ_sub_succ_eq_sub n m

theorem sub_self (n : ℕ) : n - n = 0 :=
induction_on n !sub_zero_right (take k IH, !sub_succ_succ ⬝ IH)

theorem sub_add_add_right (n k m : ℕ) : (n + k) - (m + k) = n - m :=
induction_on k
  (calc
    (n + 0) - (m + 0) = n - (m + 0) : {!add_zero}
                  ... = n - m       : {!add_zero})
  (take l : nat,
    assume IH : (n + l) - (m + l) = n - m,
    calc
      (n + succ l) - (m + succ l) = succ (n + l) - (m + succ l) : {!add_succ}
                              ... = succ (n + l) - succ (m + l) : {!add_succ}
                              ... = (n + l) - (m + l)           : !sub_succ_succ
                              ... =  n - m                      : IH)

theorem sub_add_add_left (k n m : ℕ) : (k + n) - (k + m) = n - m :=
!add.comm ▸ !add.comm ▸ !sub_add_add_right

theorem sub_add_left (n m : ℕ) : n + m - m = n :=
induction_on m
  (!add_zero⁻¹ ▸ !sub_zero_right)
  (take k : ℕ,
    assume IH : n + k - k = n,
    calc
      n + succ k - succ k = succ (n + k) - succ k : {!add_succ}
                      ... = n + k - k             : !sub_succ_succ
                      ... = n                     : IH)

-- TODO: add_sub_inv'
theorem sub_add_left2 (n m : ℕ) : n + m - n = m :=
!add.comm ▸ !sub_add_left

theorem sub_sub (n m k : ℕ) : n - m - k = n - (m + k) :=
induction_on k
  (calc
    n - m - 0 = n - m        : !sub_zero_right
          ... =  n - (m + 0) : {!add_zero⁻¹})
  (take l : nat,
    assume IH : n - m - l = n - (m + l),
    calc
      n - m - succ l = pred (n - m - l)   : !sub_succ_right
                 ... = pred (n - (m + l)) : {IH}
                 ... = n - succ (m + l)   : !sub_succ_right⁻¹
                 ... = n - (m + succ l)   : {!add_succ⁻¹})

theorem succ_sub_sub (n m k : ℕ) : succ n - m - succ k = n - m - k :=
calc
  succ n - m - succ k = succ n - (m + succ k) : !sub_sub
                  ... = succ n - succ (m + k) : {!add_succ}
                  ... = n - (m + k)           : !sub_succ_succ
                  ... = n - m - k             : !sub_sub⁻¹

theorem sub_add_right_eq_zero (n m : ℕ) : n - (n + m) = 0 :=
calc
  n - (n + m) = n - n - m : !sub_sub⁻¹
          ... = 0 - m     : {!sub_self}
          ... = 0         : !sub_zero_left

theorem sub_comm (m n k : ℕ) : m - n - k = m - k - n :=
calc
  m - n - k = m - (n + k) : !sub_sub
        ... = m - (k + n) : {!add.comm}
        ... = m - k - n   : !sub_sub⁻¹

theorem sub_one (n : ℕ) : n - 1 = pred n :=
calc
  n - 1 = pred (n - 0) : !sub_succ_right
    ... = pred n       : {!sub_zero_right}

theorem succ_sub_one (n : ℕ) : succ n - 1 = n :=
!sub_succ_succ ⬝ !sub_zero_right

-- add_rewrite sub_add_left

-- ### interaction with multiplication

theorem mul_pred_left (n m : ℕ) : pred n * m = n * m - m :=
induction_on n
  (calc
    pred 0 * m = 0 * m     : {pred.zero}
           ... = 0         : !zero_mul
           ... = 0 - m     : !sub_zero_left⁻¹
           ... = 0 * m - m : {!zero_mul⁻¹})
  (take k : nat,
    assume IH : pred k * m = k * m - m,
    calc
      pred (succ k) * m = k * m          : {!pred.succ}
                    ... = k * m + m - m  : !sub_add_left⁻¹
                    ... = succ k * m - m : {!succ_mul⁻¹})

theorem mul_pred_right (n m : ℕ) : n * pred m = n * m - n :=
calc n * pred m = pred m * n : !mul.comm
            ... = m * n - n  : !mul_pred_left
            ... = n * m - n  : {!mul.comm}

theorem mul_sub_distr_right (n m k : ℕ) : (n - m) * k = n * k - m * k :=
induction_on m
  (calc
    (n - 0) * k = n * k         : {!sub_zero_right}
            ... = n * k - 0     : !sub_zero_right⁻¹
            ... = n * k - 0 * k : {!zero_mul⁻¹})
  (take l : nat,
    assume IH : (n - l) * k = n * k - l * k,
    calc
      (n - succ l) * k = pred (n - l) * k     : {!sub_succ_right}
                   ... = (n - l) * k - k      : !mul_pred_left
                   ... = n * k - l * k - k    : {IH}
                   ... = n * k - (l * k + k)  : !sub_sub
                   ... = n * k - (succ l * k) : {!succ_mul⁻¹})

theorem mul_sub_distr_left (n m k : ℕ) : n * (m - k) = n * m - n * k :=
calc
  n * (m - k) = (m - k) * n   : !mul.comm
          ... = m * n - k * n : !mul_sub_distr_right
          ... = n * m - k * n : {!mul.comm}
          ... = n * m - n * k : {!mul.comm}

-- ### interaction with inequalities

theorem succ_sub {m n : ℕ} : m ≥ n → succ m - n  = succ (m - n) :=
sub_induction n m
  (take k,
    assume H : 0 ≤ k,
    calc
      succ k - 0 = succ k       : !sub_zero_right
             ... = succ (k - 0) : {!sub_zero_right⁻¹})
  (take k,
    assume H : succ k ≤ 0,
    absurd H !not_succ_le_zero)
  (take k l,
    assume IH : k ≤ l → succ l - k = succ (l - k),
    take H : succ k ≤ succ l,
    calc
      succ (succ l) - succ k = succ l - k             : !sub_succ_succ
                         ... = succ (l - k)           : IH (le_of_succ_le_succ H)
                         ... = succ (succ l - succ k) : {!sub_succ_succ⁻¹})

theorem le_imp_sub_eq_zero {n m : ℕ} (H : n ≤ m) : n - m = 0 :=
obtain (k : ℕ) (Hk : n + k = m), from le.elim H, Hk ▸ !sub_add_right_eq_zero

theorem add_sub_le {n m : ℕ} : n ≤ m → n + (m - n) = m :=
sub_induction n m
  (take k,
    assume H : 0 ≤ k,
    calc
      0 + (k - 0) = k - 0 : !zero_add
              ... = k     : !sub_zero_right)
  (take k, assume H : succ k ≤ 0, absurd H !not_succ_le_zero)
  (take k l,
    assume IH : k ≤ l → k + (l - k) = l,
    take H : succ k ≤ succ l,
    calc
      succ k + (succ l - succ k) = succ k + (l - k)   : {!sub_succ_succ}
                             ... = succ (k + (l - k)) : !add.succ_left
                             ... = succ l             : {IH (le_of_succ_le_succ H)})

theorem add_sub_ge_left {n m : ℕ} : n ≥ m → n - m + m = n :=
!add.comm ▸ !add_sub_le

theorem add_sub_ge {n m : ℕ} (H : n ≥ m) : n + (m - n) = n :=
calc
  n + (m - n) = n + 0 : {le_imp_sub_eq_zero H}
          ... = n     : !add_zero

theorem add_sub_le_left {n m : ℕ} : n ≤ m → n - m + m = m :=
!add.comm ▸ add_sub_ge

theorem le_add_sub_left (n m : ℕ) : n ≤ n + (m - n) :=
or.elim !le.total
  (assume H : n ≤ m, (add_sub_le H)⁻¹ ▸ H)
  (assume H : m ≤ n, (add_sub_ge H)⁻¹ ▸ !le.refl)

theorem le_add_sub_right (n m : ℕ) : m ≤ n + (m - n) :=
or.elim !le.total
  (assume H : n ≤ m, (add_sub_le H)⁻¹ ▸ !le.refl)
  (assume H : m ≤ n, (add_sub_ge H)⁻¹ ▸ H)

theorem sub_split {P : ℕ → Prop} {n m : ℕ} (H1 : n ≤ m → P 0) (H2 : ∀k, m + k = n -> P k)
  : P (n - m) :=
or.elim !le.total
  (assume H3 : n ≤ m, (le_imp_sub_eq_zero H3)⁻¹ ▸ (H1 H3))
  (assume H3 : m ≤ n, H2 (n - m) (add_sub_le H3))

theorem le_elim_sub {n m : ℕ} (H : n ≤ m) : ∃k, m - k = n :=
obtain (k : ℕ) (Hk : n + k = m), from le.elim H,
exists.intro k
  (calc
    m - k = n + k - k : {Hk⁻¹}
      ... = n         : !sub_add_left)

theorem add_sub_assoc {m k : ℕ} (H : k ≤ m) (n : ℕ) : n + m - k = n + (m - k) :=
have l1 : k ≤ m → n + m - k = n + (m - k), from
  sub_induction k m
    (take m : ℕ,
      assume H : 0 ≤ m,
      calc
        n + m - 0 = n + m       : !sub_zero_right
              ... = n + (m - 0) : {!sub_zero_right⁻¹})
    (take k : ℕ, assume H : succ k ≤ 0, absurd H !not_succ_le_zero)
    (take k m,
      assume IH : k ≤ m → n + m - k = n + (m - k),
      take H : succ k ≤ succ m,
      calc
        n + succ m - succ k = succ (n + m) - succ k : {!add_succ}
                        ... = n + m - k             : !sub_succ_succ
                        ... = n + (m - k)           : IH (le_of_succ_le_succ H)
                        ... = n + (succ m - succ k) : {!sub_succ_succ⁻¹}),
l1 H

theorem sub_eq_zero_imp_le {n m : ℕ} : n - m = 0 → n ≤ m :=
sub_split
  (assume H1 : n ≤ m, assume H2 : 0 = 0, H1)
  (take k : ℕ,
    assume H1 : m + k = n,
    assume H2 : k = 0,
    have H3 : n = m, from !add_zero ▸ H2 ▸ H1⁻¹,
    H3 ▸ !le.refl)

theorem sub_sub_split {P : ℕ → ℕ → Prop} {n m : ℕ} (H1 : ∀k, n = m + k -> P k 0)
  (H2 : ∀k, m = n + k → P 0 k) : P (n - m) (m - n) :=
or.elim !le.total
  (assume H3 : n ≤ m,
    le_imp_sub_eq_zero H3⁻¹ ▸  (H2 (m - n) (add_sub_le H3⁻¹)))
  (assume H3 : m ≤ n,
    le_imp_sub_eq_zero H3⁻¹ ▸ (H1 (n - m) (add_sub_le H3⁻¹)))

theorem sub_intro {n m k : ℕ} (H : n + m = k) : k - n = m :=
have H2 : k - n + n = m + n, from
  calc
    k - n + n = k     : add_sub_ge_left (le.intro H)
          ... = n + m : H⁻¹
          ... = m + n : !add.comm,
add.cancel_right H2

theorem sub_lt {x y : ℕ} (xpos : x > 0) (ypos : y > 0) : x - y < x :=
sub.lt xpos ypos

theorem sub_le_right {n m : ℕ} (H : n ≤ m) (k : nat) : n - k ≤ m - k :=
obtain (l : ℕ) (Hl : n + l = m), from le.elim H,
or.elim !le.total
  (assume H2 : n ≤ k, (le_imp_sub_eq_zero H2)⁻¹ ▸ !zero_le)
  (assume H2 : k ≤ n,
    have H3 : n - k + l = m - k, from
      calc
        n - k + l = l + (n - k) : add.comm
              ... = l + n - k   : (add_sub_assoc H2 l)⁻¹
              ... = n + l - k   : {!add.comm}
              ... = m - k       : {Hl},
    le.intro H3)

theorem sub_le_left {n m : ℕ} (H : n ≤ m) (k : nat) : k - m ≤ k - n :=
obtain (l : ℕ) (Hl : n + l = m), from le.elim H,
sub_split
  (assume H2 : k ≤ m, !zero_le)
  (take m' : ℕ,
    assume Hm : m + m' = k,
    have H3 : n ≤ k, from le.trans H (le.intro Hm),
    have H4 : m' + l + n = k - n + n, from
      calc
        m' + l + n = n + (m' + l) : add.comm
               ... = n + (l + m') : add.comm
               ... = n + l + m'   : add.assoc
               ... = m + m'       : {Hl}
               ... = k            : Hm
               ... = k - n + n    : (add_sub_ge_left H3)⁻¹,
    le.intro (add.cancel_right H4))

theorem sub_pos_of_gt {m n : ℕ} (H : n > m) : n - m > 0 :=
have H1 : n = n - m + m, from (add_sub_ge_left (le.of_lt H))⁻¹,
have H2 : 0 + m < n - m + m, from (zero_add m)⁻¹ ▸ H1 ▸ H,
!lt_of_add_lt_add_right H2

-- theorem sub_lt_cancel_right {n m k : ℕ) (H : n - k < m - k) : n < m
-- :=
--   _

-- theorem sub_lt_cancel_left {n m k : ℕ) (H : n - m < n - k) : k < m
-- :=
--   _

theorem sub_triangle_inequality (n m k : ℕ) : n - k ≤ (n - m) + (m - k) :=
sub_split
  (assume H : n ≤ m, !zero_add⁻¹ ▸ sub_le_right H k)
  (take mn : ℕ,
    assume Hmn : m + mn = n,
    sub_split
      (assume H : m ≤ k,
        have H2 : n - k ≤ n - m, from sub_le_left H n,
        have H3 : n - k ≤ mn, from sub_intro Hmn ▸ H2,
        show n - k ≤ mn + 0, from !add_zero⁻¹ ▸ H3)
      (take km : ℕ,
        assume Hkm : k + km = m,
        have H : k + (mn + km) = n, from
          calc
            k + (mn + km) = k + (km + mn): add.comm
                      ... = k + km + mn  : add.assoc
                      ... = m + mn       : Hkm
                      ... = n            : Hmn,
        have H2 : n - k = mn + km, from sub_intro H,
        H2 ▸ !le.refl))


-- add_rewrite sub_self mul_sub_distr_left mul_sub_distr_right


-- absolute difference
-- --------------------------------------------

-- ### absolute difference

-- This section is still incomplete

definition dist (n m : ℕ) := (n - m) + (m - n)

theorem dist_comm (n m : ℕ) : dist n m = dist m n :=
!add.comm

theorem dist_self (n : ℕ) : dist n n = 0 :=
calc
  (n - n) + (n - n) = 0 + (n - n) : sub_self
                ... = 0 + 0       : sub_self
                ... = 0           : rfl

theorem dist_eq_zero {n m : ℕ} (H : dist n m = 0) : n = m :=
have H2 : n - m = 0, from eq_zero_of_add_eq_zero_right H,
have H3 : n ≤ m, from sub_eq_zero_imp_le H2,
have H4 : m - n = 0, from eq_zero_of_add_eq_zero_left H,
have H5 : m ≤ n, from sub_eq_zero_imp_le H4,
le.antisymm H3 H5

theorem dist_le {n m : ℕ} (H : n ≤ m) : dist n m = m - n :=
calc
  dist n m = 0 + (m - n) : {le_imp_sub_eq_zero H}
       ... = m - n       : !zero_add

theorem dist_ge {n m : ℕ} (H : n ≥ m) : dist n m = n - m :=
!dist_comm ▸ dist_le H

theorem dist_zero_right (n : ℕ) : dist n 0 = n :=
dist_ge !zero_le ⬝ !sub_zero_right

theorem dist_zero_left (n : ℕ) : dist 0 n = n :=
dist_le !zero_le ⬝ !sub_zero_right

theorem dist_intro {n m k : ℕ} (H : n + m = k) : dist k n = m :=
calc
  dist k n = k - n : dist_ge (le.intro H)
           ... = m : sub_intro H

theorem dist_add_right (n k m : ℕ) : dist (n + k) (m + k) = dist n m :=
calc
  dist (n + k) (m + k) = ((n+k) - (m+k)) + ((m+k)-(n+k)) : rfl
                   ... = (n - m) + ((m + k) - (n + k))   : {!sub_add_add_right}
                   ... = (n - m) + (m - n)               : {!sub_add_add_right}

theorem dist_add_left (k n m : ℕ) : dist (k + n) (k + m) = dist n m :=
!add.comm ▸ !add.comm ▸ !dist_add_right

-- add_rewrite dist_self dist_add_right dist_add_left dist_zero_left dist_zero_right

theorem dist_ge_add_right {n m : ℕ} (H : n ≥ m) : dist n m + m = n :=
calc
  dist n m + m = n - m + m : {dist_ge H}
           ... = n         : add_sub_ge_left H

theorem dist_eq_intro {n m k l : ℕ} (H : n + m = k + l) : dist n k = dist l m :=
calc
  dist n k = dist (n + m) (k + m) : !dist_add_right⁻¹
       ... = dist (k + l) (k + m) : {H}
       ... = dist l m             : !dist_add_left

theorem dist_sub_move_add {n m : ℕ} (H : n ≥ m) (k : ℕ) : dist (n - m) k = dist n (k + m) :=
have H2 : n - m + (k + m) = k + n, from
  calc
    n - m + (k + m) = n - m + (m + k) : add.comm
                ... = n - m + m + k   : add.assoc
                ... = n + k           : {add_sub_ge_left H}
                ... = k + n           : add.comm,
dist_eq_intro H2

theorem dist_sub_move_add' {k m : ℕ} (H : k ≥ m) (n : ℕ) : dist n (k - m) = dist (n + m) k :=
(dist_sub_move_add H n ▸ !dist_comm) ▸ !dist_comm

--triangle inequality formulated with dist
theorem triangle_inequality (n m k : ℕ) : dist n k ≤ dist n m + dist m k :=
have H : (n - m) + (m - k) + ((k - m) + (m - n)) = (n - m) + (m - n) + ((m - k) + (k - m)),
  by simp,
H ▸ add_le_add !sub_triangle_inequality !sub_triangle_inequality

theorem dist_add_le_add_dist (n m k l : ℕ) : dist (n + m) (k + l) ≤ dist n k + dist m l :=
have H : dist (n + m) (k + m) + dist (k + m) (k + l) = dist n k + dist m l, from
  !dist_add_left ▸ !dist_add_right ▸ rfl,
H ▸ !triangle_inequality

--interaction with multiplication

theorem dist_mul_left (k n m : ℕ) : dist (k * n) (k * m) = k * dist n m :=
have H : ∀n m, dist n m = n - m + (m - n), from take n m, rfl,
by simp

theorem dist_mul_right (n k m : ℕ) : dist (n * k) (m * k) = dist n m * k :=
have H : ∀n m, dist n m = n - m + (m - n), from take n m, rfl,
by simp

-- add_rewrite dist_mul_right dist_mul_left dist_comm

--needed to prove of_nat a * of_nat b = of_nat (a * b) in int
theorem dist_mul_dist (n m k l : ℕ) : dist n m * dist k l = dist (n * k + m * l) (n * l + m * k) :=
have aux : ∀k l, k ≥ l → dist n m * dist k l = dist (n * k + m * l) (n * l + m * k), from
  take k l : ℕ,
  assume H : k ≥ l,
  have H2 : m * k ≥ m * l, from mul_le_mul_left H m,
  have H3 : n * l + m * k ≥ m * l, from le.trans H2 !le_add_left,
  calc
    dist n m * dist k l = dist n m * (k - l)       : {dist_ge H}
      ... = dist (n * (k - l)) (m * (k - l))       : !dist_mul_right⁻¹
      ... = dist (n * k - n * l) (m * k - m * l)   : by simp
      ... = dist (n * k) (m * k - m * l + n * l)   : dist_sub_move_add (mul_le_mul_left H n) _
      ... = dist (n * k) (n * l + (m * k - m * l)) : {!add.comm}
      ... = dist (n * k) (n * l + m * k - m * l)   : {(add_sub_assoc H2 (n * l))⁻¹}
      ... = dist (n * k + m * l) (n * l + m * k)   : dist_sub_move_add' H3 _,
or.elim !le.total
  (assume H : k ≤ l, !dist_comm ▸ !dist_comm ▸ aux l k H)
  (assume H : l ≤ k, aux k l H)

end nat
