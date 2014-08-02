----------------------------------------------------------------------------------------------------
--- Copyright (c) 2014 Floris van Doorn. All rights reserved.
--- Released under Apache 2.0 license as described in the file LICENSE.
--- Author: Floris van Doorn
----------------------------------------------------------------------------------------------------

import data.nat.order
using nat eq_proofs tactic
using helper_tactics

namespace nat

-- data.nat.basic2
-- ===============
--
-- More basic operations on the natural numbers.

-- subtraction
-- -----------

definition sub (n m : ℕ) : nat := nat_rec n (fun m x, pred x) m
infixl `-` : 65 := sub

theorem sub_zero_right (n : ℕ) : n - 0 = n

theorem sub_succ_right (n m : ℕ) : n - succ m = pred (n - m)

opaque_hint (hiding sub)

theorem sub_zero_left (n : ℕ) : 0 - n = 0 :=
induction_on n (sub_zero_right 0)
  (take k : nat,
    assume IH : 0 - k = 0,
    calc
      0 - succ k = pred (0 - k) : sub_succ_right 0 k
	... = pred 0 : {IH}
	... = 0 : pred_zero)
--(
--theorem sub_succ_left (n m : ℕ) : pred (succ n - m) = n - m
-- :=
--   induction_on m
--     (calc
--       pred (succ n - 0) = pred (succ n) : {sub_zero_right (succ n)}
--         ... = n : pred_succ n
--         ... = n - 0 : symm (sub_zero_right n))
--     (take k : nat,
--       assume IH : pred (succ n - k) = n - k,
--       _)
--)

--succ_sub_succ
theorem sub_succ_succ (n m : ℕ) : succ n - succ m = n - m :=
induction_on m
  (calc
    succ n - 1 = pred (succ n - 0) : sub_succ_right (succ n) 0
      ... = pred (succ n) : {sub_zero_right (succ n)}
      ... = n : pred_succ n
      ... = n - 0 : symm (sub_zero_right n))
  (take k : nat,
    assume IH : succ n - succ k = n - k,
    calc
      succ n - succ (succ k) = pred (succ n - succ k) : sub_succ_right (succ n) (succ k)
	... = pred (n - k) : {IH}
	... = n - succ k : symm (sub_succ_right n k))

theorem sub_self (n : ℕ) : n - n = 0 :=
induction_on n (sub_zero_right 0) (take k IH, trans (sub_succ_succ k k) IH)

-- TODO: add_sub_add_right
theorem sub_add_add_right (n k m : ℕ) : (n + k) - (m + k) = n - m :=
induction_on k
  (calc
    (n + 0) - (m + 0) = n - (m + 0) : {add_zero_right _}
      ... = n - m : {add_zero_right _})
  (take l : nat,
    assume IH : (n + l) - (m + l) = n - m,
    calc
      (n + succ l) - (m + succ l) = succ (n + l) - (m + succ l) : {add_succ_right _ _}
	... = succ (n + l) - succ (m + l) : {add_succ_right _ _}
	... = (n + l) - (m + l) : sub_succ_succ _ _
	... =  n - m : IH)

theorem sub_add_add_left (k n m : ℕ) : (k + n) - (k + m) = n - m :=
add_comm m k ▸ add_comm n k ▸ sub_add_add_right n k m

-- TODO: add_sub_inv
theorem sub_add_left (n m : ℕ) : n + m - m = n :=
induction_on m
  ((add_zero_right n)⁻¹ ▸ sub_zero_right n)
  (take k : ℕ,
    assume IH : n + k - k = n,
    calc
      n + succ k - succ k = succ (n + k) - succ k : {add_succ_right n k}
	... = n + k - k : sub_succ_succ _ _
	... = n : IH)

-- TODO: add_sub_inv'
theorem sub_add_left2 (n m : ℕ) : n + m - n = m :=
add_comm m n ▸ sub_add_left m n

theorem sub_sub (n m k : ℕ) : n - m - k = n - (m + k) :=
induction_on k
  (calc
    n - m - 0 = n - m : sub_zero_right _
      ... =  n - (m + 0) : {symm (add_zero_right m)})
  (take l : nat,
    assume IH : n - m - l = n - (m + l),
    calc
      n - m - succ l = pred (n - m - l) : sub_succ_right (n - m) l
	... = pred (n - (m + l)) : {IH}
	... = n - succ (m + l) : symm (sub_succ_right n (m + l))
	... = n - (m + succ l) : {symm (add_succ_right m l)})

theorem succ_sub_sub (n m k : ℕ) : succ n - m - succ k = n - m - k :=
calc
  succ n - m - succ k = succ n - (m + succ k) : sub_sub _ _ _
    ... = succ n - succ (m + k) : {add_succ_right m k}
    ... = n - (m + k) : sub_succ_succ _ _
    ... = n - m - k : symm (sub_sub n m k)

theorem sub_add_right_eq_zero (n m : ℕ) : n - (n + m) = 0 :=
calc
  n - (n + m) = n - n - m : symm (sub_sub n n m)
    ... = 0 - m : {sub_self n}
    ... = 0 : sub_zero_left m

theorem sub_comm (m n k : ℕ) : m - n - k = m - k - n :=
calc
  m - n - k = m - (n + k) : sub_sub m n k
    ... = m - (k + n) : {add_comm n k}
    ... = m - k - n : symm (sub_sub m k n)

theorem sub_one (n : ℕ) : n - 1 = pred n :=
calc
  n - 1 = pred (n - 0) : sub_succ_right n 0
    ... = pred n : {sub_zero_right n}

theorem succ_sub_one (n : ℕ) : succ n - 1 = n :=
trans (sub_succ_succ n 0) (sub_zero_right n)

-- add_rewrite sub_add_left

-- ### interaction with multiplication

theorem mul_pred_left (n m : ℕ) : pred n * m = n * m - m :=
induction_on n
  (calc
    pred 0 * m = 0 * m : {pred_zero}
      ... = 0 : mul_zero_left _
      ... = 0 - m : symm (sub_zero_left m)
      ... = 0 * m - m : {symm (mul_zero_left m)})
  (take k : nat,
    assume IH : pred k * m = k * m - m,
    calc
      pred (succ k) * m = k * m : {pred_succ k}
	... = k * m + m - m : symm (sub_add_left _ _)
	... = succ k * m - m : {symm (mul_succ_left k m)})

theorem mul_pred_right (n m : ℕ) : n * pred m = n * m - n :=
calc n * pred m = pred m * n : mul_comm _ _
  ... = m * n - n : mul_pred_left m n
  ... = n * m - n : {mul_comm m n}

theorem mul_sub_distr_right (n m k : ℕ) : (n - m) * k = n * k - m * k :=
induction_on m
  (calc
    (n - 0) * k = n * k : {sub_zero_right n}
      ... = n * k - 0 : symm (sub_zero_right _)
      ... = n * k - 0 * k : {symm (mul_zero_left _)})
  (take l : nat,
    assume IH : (n - l) * k = n * k - l * k,
    calc
      (n - succ l) * k = pred (n - l) * k : {sub_succ_right n l}
	... = (n - l) * k - k : mul_pred_left _ _
	... = n * k - l * k - k : {IH}
	... = n * k - (l * k + k) : sub_sub _ _ _
	... = n * k - (succ l * k) : {symm (mul_succ_left l k)})

theorem mul_sub_distr_left (n m k : ℕ) : n * (m - k) = n * m - n * k :=
calc
  n * (m - k) = (m - k) * n : mul_comm _ _
    ... = m * n - k * n : mul_sub_distr_right _ _ _
    ... = n * m - k * n : {mul_comm _ _}
    ... = n * m - n * k : {mul_comm _ _}

-- ### interaction with inequalities

theorem succ_sub {m n : ℕ} : m ≥ n → succ m - n  = succ (m - n) :=
sub_induction n m
  (take k,
    assume H : 0 ≤ k,
    calc
      succ k - 0 = succ k : sub_zero_right (succ k)
	... = succ (k - 0) : {symm (sub_zero_right k)})
  (take k,
    assume H : succ k ≤ 0,
    absurd_elim _ H (not_succ_zero_le k))
  (take k l,
    assume IH : k ≤ l → succ l - k = succ (l - k),
    take H : succ k ≤ succ l,
    calc
      succ (succ l) - succ k = succ l - k : sub_succ_succ (succ l) k
	... = succ (l - k) : IH (succ_le_cancel H)
	... = succ (succ l - succ k) : {symm (sub_succ_succ l k)})

theorem le_imp_sub_eq_zero {n m : ℕ} (H : n ≤ m) : n - m = 0 :=
obtain (k : ℕ) (Hk : n + k = m), from le_elim H, Hk ▸ sub_add_right_eq_zero n k

theorem add_sub_le {n m : ℕ} : n ≤ m → n + (m - n) = m :=
sub_induction n m
  (take k,
    assume H : 0 ≤ k,
    calc
      0 + (k - 0) = k - 0 : add_zero_left (k - 0)
	... = k : sub_zero_right k)
  (take k, assume H : succ k ≤ 0, absurd_elim _ H (not_succ_zero_le k))
  (take k l,
    assume IH : k ≤ l → k + (l - k) = l,
    take H : succ k ≤ succ l,
    calc
      succ k + (succ l - succ k) = succ k + (l - k) : {sub_succ_succ l k}
	... = succ (k + (l - k)) : add_succ_left k (l - k)
	... = succ l : {IH (succ_le_cancel H)})

theorem add_sub_ge_left {n m : ℕ} : n ≥ m → n - m + m = n :=
add_comm m (n - m) ▸ add_sub_le

theorem add_sub_ge {n m : ℕ} (H : n ≥ m) : n + (m - n) = n :=
calc
  n + (m - n) = n + 0 : {le_imp_sub_eq_zero H}
    ... = n : add_zero_right n

theorem add_sub_le_left {n m : ℕ} : n ≤ m → n - m + m = m :=
add_comm m (n - m) ▸ add_sub_ge

theorem le_add_sub_left (n m : ℕ) : n ≤ n + (m - n) :=
or_elim (le_total n m)
  (assume H : n ≤ m, (add_sub_le H)⁻¹ ▸ H)
  (assume H : m ≤ n, (add_sub_ge H)⁻¹ ▸ le_refl n)

theorem le_add_sub_right (n m : ℕ) : m ≤ n + (m - n) :=
or_elim (le_total n m)
  (assume H : n ≤ m, subst (symm (add_sub_le H)) (le_refl m))
  (assume H : m ≤ n, subst (symm (add_sub_ge H)) H)

theorem sub_split {P : ℕ → Prop} {n m : ℕ} (H1 : n ≤ m → P 0) (H2 : ∀k, m + k = n -> P k)
  : P (n - m) :=
or_elim (le_total n m)
  (assume H3 : n ≤ m, subst (symm (le_imp_sub_eq_zero H3)) (H1 H3))
  (assume H3 : m ≤ n, H2 (n - m) (add_sub_le H3))

theorem sub_le_self (n m : ℕ) : n - m ≤ n :=
sub_split
  (assume H : n ≤ m, zero_le n)
  (take k : ℕ, assume H : m + k = n, le_intro (subst (add_comm m k) H))

theorem le_elim_sub (n m : ℕ) (H : n ≤ m) : ∃k, m - k = n :=
obtain (k : ℕ) (Hk : n + k = m), from le_elim H,
exists_intro k
  (calc
    m - k = n + k - k : {symm Hk}
      ... = n : sub_add_left n k)

theorem add_sub_assoc {m k : ℕ} (H : k ≤ m) (n : ℕ) : n + m - k = n + (m - k) :=
have l1 : k ≤ m → n + m - k = n + (m - k), from
  sub_induction k m
    (take m : ℕ,
      assume H : 0 ≤ m,
      calc
	n + m - 0 = n + m : sub_zero_right (n + m)
	  ... = n + (m - 0) : {symm (sub_zero_right m)})
    (take k : ℕ, assume H : succ k ≤ 0, absurd_elim _ H (not_succ_zero_le k))
    (take k m,
      assume IH : k ≤ m → n + m - k = n + (m - k),
      take H : succ k ≤ succ m,
      calc
	n + succ m - succ k = succ (n + m) - succ k : {add_succ_right n m}
	  ... = n + m - k : sub_succ_succ (n + m) k
	  ... = n + (m - k) : IH (succ_le_cancel H)
	  ... = n + (succ m - succ k) : {symm (sub_succ_succ m k)}),
l1 H

theorem sub_eq_zero_imp_le {n m : ℕ} : n - m = 0 → n ≤ m :=
sub_split
  (assume H1 : n ≤ m, assume H2 : 0 = 0, H1)
  (take k : ℕ,
    assume H1 : m + k = n,
    assume H2 : k = 0,
    have H3 : n = m, from subst (add_zero_right m) (subst H2 (symm H1)),
    subst H3 (le_refl n))

theorem sub_sub_split {P : ℕ → ℕ → Prop} {n m : ℕ} (H1 : ∀k, n = m + k -> P k 0)
  (H2 : ∀k, m = n + k → P 0 k) : P (n - m) (m - n) :=
or_elim (le_total n m)
  (assume H3 : n ≤ m,
    le_imp_sub_eq_zero H3⁻¹ ▸  (H2 (m - n) (add_sub_le H3⁻¹)))
  (assume H3 : m ≤ n,
    le_imp_sub_eq_zero H3⁻¹ ▸ (H1 (n - m) (add_sub_le H3⁻¹)))

theorem sub_intro {n m k : ℕ} (H : n + m = k) : k - n = m :=
have H2 : k - n + n = m + n, from
  calc
    k - n + n = k : add_sub_ge_left (le_intro H)
      ... = n + m : symm H
      ... = m + n : add_comm n m,
add_cancel_right H2

theorem sub_lt {x y : ℕ} (xpos : x > 0) (ypos : y > 0) : x - y < x :=
obtain (x' : ℕ) (xeq : x = succ x'), from pos_imp_eq_succ xpos,
 obtain (y' : ℕ) (yeq : y = succ y'), from pos_imp_eq_succ ypos,
 have xsuby_eq : x - y = x' - y', from
   calc
     x - y = succ x' - y : {xeq}
       ... = succ x' - succ y' : {yeq}
       ... = x' - y' : sub_succ_succ _ _,
 have H1 : x' - y' ≤ x', from sub_le_self _ _,
 have H2 : x' < succ x', from self_lt_succ _,
 show x - y < x, from xeq⁻¹ ▸ xsuby_eq⁻¹ ▸ le_lt_trans H1 H2

theorem sub_le_right {n m : ℕ} (H : n ≤ m) (k : nat) : n - k ≤ m - k :=
obtain (l : ℕ) (Hl : n + l = m), from le_elim H,
or_elim (le_total n k)
  (assume H2 : n ≤ k, (le_imp_sub_eq_zero H2)⁻¹ ▸ zero_le (m - k))
  (assume H2 : k ≤ n,
    have H3 : n - k + l = m - k, from
      calc
	n - k + l = l + (n - k) : by simp
	  ... = l + n - k : symm (add_sub_assoc H2 l)
	  ... = n + l - k : {add_comm l n}
	  ... = m - k : {Hl},
    le_intro H3)

theorem sub_le_left {n m : ℕ} (H : n ≤ m) (k : nat) : k - m ≤ k - n :=
obtain (l : ℕ) (Hl : n + l = m), from le_elim H,
sub_split
  (assume H2 : k ≤ m, zero_le (k - n))
  (take m' : ℕ,
    assume Hm : m + m' = k,
    have H3 : n ≤ k, from le_trans H (le_intro Hm),
    have H4 : m' + l + n = k - n + n, from
      calc
	m' + l + n = n + l + m' : by simp
	  ... = m + m' : {Hl}
	  ... = k : Hm
	  ... = k - n + n : symm (add_sub_ge_left H3),
    le_intro (add_cancel_right H4))

-- theorem sub_lt_cancel_right {n m k : ℕ) (H : n - k < m - k) : n < m
-- :=
--   _

-- theorem sub_lt_cancel_left {n m k : ℕ) (H : n - m < n - k) : k < m
-- :=
--   _

theorem sub_triangle_inequality (n m k : ℕ) : n - k ≤ (n - m) + (m - k) :=
sub_split
  (assume H : n ≤ m, (add_zero_left (m - k))⁻¹ ▸ sub_le_right H k)
  (take mn : ℕ,
    assume Hmn : m + mn = n,
    sub_split
      (assume H : m ≤ k,
	have H2 : n - k ≤ n - m, from sub_le_left H n,
	have H3 : n - k ≤ mn, from sub_intro Hmn ▸ H2,
	show n - k ≤ mn + 0, from (add_zero_right mn)⁻¹ ▸ H3)
      (take km : ℕ,
	assume Hkm : k + km = m,
	have H : k + (mn + km) = n, from
	  calc
	    k + (mn + km) = k + km + mn : by simp
	      ... = m + mn : {Hkm}
	      ... = n : Hmn,
	have H2 : n - k = mn + km, from sub_intro H,
	H2 ▸ (le_refl (n - k))))


-- add_rewrite sub_self mul_sub_distr_left mul_sub_distr_right


-- Max, min, iteration, and absolute difference
-- --------------------------------------------

definition max (n m : ℕ) : ℕ := n + (m - n)
definition min (n m : ℕ) : ℕ := m - (m - n)

theorem max_le {n m : ℕ} (H : n ≤ m) : n + (m - n) = m := add_sub_le H

theorem max_ge {n m : ℕ} (H : n ≥ m) : n + (m - n) = n := add_sub_ge H

theorem left_le_max (n m : ℕ) : n ≤ n + (m - n) := le_add_sub_left n m

theorem right_le_max (n m : ℕ) : m ≤ max n m := le_add_sub_right n m

-- ### absolute difference

-- This section is still incomplete

definition dist (n m : ℕ) := (n - m) + (m - n)

theorem dist_comm (n m : ℕ) : dist n m = dist m n :=
add_comm (n - m) (m - n)

theorem dist_self (n : ℕ) : dist n n = 0 :=
calc
  (n - n) + (n - n) = 0 + 0 : by simp
    ... = 0 : by simp

theorem dist_eq_zero {n m : ℕ} (H : dist n m = 0) : n = m :=
have H2 : n - m = 0, from add_eq_zero_left H,
have H3 : n ≤ m, from sub_eq_zero_imp_le H2,
have H4 : m - n = 0, from add_eq_zero_right H,
have H5 : m ≤ n, from sub_eq_zero_imp_le H4,
le_antisym H3 H5

theorem dist_le {n m : ℕ} (H : n ≤ m) : dist n m = m - n :=
calc
  dist n m = 0 + (m - n) : {le_imp_sub_eq_zero H}
    ... = m - n : add_zero_left (m - n)

theorem dist_ge {n m : ℕ} (H : n ≥ m) : dist n m = n - m :=
dist_comm m n ▸ dist_le H

theorem dist_zero_right (n : ℕ) : dist n 0 = n :=
trans (dist_ge (zero_le n)) (sub_zero_right n)

theorem dist_zero_left (n : ℕ) : dist 0 n = n :=
trans (dist_le (zero_le n)) (sub_zero_right n)

theorem dist_intro {n m k : ℕ} (H : n + m = k) : dist k n = m :=
calc
  dist k n = k - n : dist_ge (le_intro H)
    ... = m : sub_intro H

theorem dist_add_right (n k m : ℕ) : dist (n + k) (m + k) = dist n m :=
calc
  dist (n + k) (m + k) = ((n+k) - (m+k)) + ((m+k)-(n+k)) : refl _
    ... = (n - m) + ((m + k) - (n + k))   : {sub_add_add_right _ _ _}
    ... = (n - m) + (m - n)               : {sub_add_add_right _ _ _}

theorem dist_add_left (k n m : ℕ) : dist (k + n) (k + m) = dist n m :=
add_comm m k ▸ add_comm n k ▸ dist_add_right n k m

-- add_rewrite dist_self dist_add_right dist_add_left dist_zero_left dist_zero_right

theorem dist_ge_add_right {n m : ℕ} (H : n ≥ m) : dist n m + m = n :=
calc
  dist n m + m = n - m + m : {dist_ge H}
    ... = n : add_sub_ge_left H

theorem dist_eq_intro {n m k l : ℕ} (H : n + m = k + l) : dist n k = dist l m :=
calc
  dist n k = dist (n + m) (k + m) : symm (dist_add_right n m k)
    ... = dist (k + l) (k + m) : {H}
    ... = dist l m : dist_add_left k l m

theorem dist_sub_move_add {n m : ℕ} (H : n ≥ m) (k : ℕ) : dist (n - m) k = dist n (k + m) :=
have H2 : n - m + (k + m) = k + n, from
  calc
    n - m + (k + m) = n - m + m + k : by simp
      ... = n + k : {add_sub_ge_left H}
      ... = k + n : by simp,
dist_eq_intro H2

theorem dist_sub_move_add' {k m : ℕ} (H : k ≥ m) (n : ℕ) : dist n (k - m) = dist (n + m) k :=
subst (subst (dist_sub_move_add H n) (dist_comm (k - m) n)) (dist_comm k (n + m))

--triangle inequality formulated with dist
theorem triangle_inequality (n m k : ℕ) : dist n k ≤ dist n m + dist m k :=
have H : (n - m) + (m - k) + ((k - m) + (m - n)) = (n - m) + (m - n) + ((m - k) + (k - m)),
  by simp,
H ▸ add_le (sub_triangle_inequality n m k) (sub_triangle_inequality k m n)

theorem dist_add_le_add_dist (n m k l : ℕ) : dist (n + m) (k + l) ≤ dist n k + dist m l :=
have H : dist (n + m) (k + m) + dist (k + m) (k + l) = dist n k + dist m l, from
  calc
    _ = dist n k + dist (k + m) (k + l) : {dist_add_right n m k}
  ... = _ : {dist_add_left k m l},
H ▸ (triangle_inequality (n + m) (k + m) (k + l))

--interaction with multiplication

theorem dist_mul_left (k n m : ℕ) : dist (k * n) (k * m) = k * dist n m :=
have H : ∀n m, dist n m = n - m + (m - n), from take n m, refl _,
by simp

theorem dist_mul_right (n k m : ℕ) : dist (n * k) (m * k) = dist n m * k :=
have H : ∀n m, dist n m = n - m + (m - n), from take n m, refl _,
by simp

-- add_rewrite dist_mul_right dist_mul_left dist_comm

--needed to prove |a| * |b| = |a * b| in int
theorem dist_mul_dist (n m k l : ℕ) : dist n m * dist k l = dist (n * k + m * l) (n * l + m * k) :=
have aux : ∀k l, k ≥ l → dist n m * dist k l = dist (n * k + m * l) (n * l + m * k), from
  take k l : ℕ,
  assume H : k ≥ l,
  have H2 : m * k ≥ m * l, from mul_le_left H m,
  have H3 : n * l + m * k ≥ m * l, from le_trans H2 (le_add_left _ _),
  calc
    dist n m * dist k l = dist n m * (k - l) : {dist_ge H}
      ... = dist (n * (k - l)) (m * (k - l)) : symm (dist_mul_right n (k - l) m)
      ... = dist (n * k - n * l) (m * k - m * l) : by simp
      ... = dist (n * k) (m * k - m * l + n * l) : dist_sub_move_add (mul_le_left H n) _
      ... = dist (n * k) (n * l + (m * k - m * l)) : {add_comm _ _}
      ... = dist (n * k) (n * l + m * k - m * l) : {symm (add_sub_assoc H2 (n * l))}
      ... = dist (n * k + m * l) (n * l + m * k) : dist_sub_move_add' H3 _,
or_elim (le_total k l)
  (assume H : k ≤ l, dist_comm l k ▸ dist_comm _ _ ▸ aux l k H)
  (assume H : l ≤ k, aux k l H)

opaque_hint (hiding dist)

end -- namespace nat