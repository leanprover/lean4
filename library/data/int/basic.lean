-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Floris van Doorn, Jeremy Avigad

-- int.basic
-- =========

-- The integers, with addition, multiplication, and subtraction.

import data.nat.basic data.nat.order data.nat.sub data.prod data.quotient tools.tactic algebra.relation
import algebra.binary
import tools.fake_simplifier

open nat
open quotient subtype prod relation
open decidable binary fake_simplifier
open eq.ops

namespace int
-- ## The defining equivalence relation on ℕ × ℕ
definition rel (a b : ℕ × ℕ) : Prop :=  pr1 a + pr2 b = pr2 a + pr1 b

theorem rel_comp (n m k l : ℕ) : (rel (pair n m) (pair k l)) ↔ (n + l = m + k) :=
have H : (pr1 (pair n m) + pr2 (pair k l) = pr2 (pair n m) + pr1 (pair k l)) ↔ (n + l = m + k),
  by simp,
H

-- add_rewrite rel_comp --local

theorem rel_refl {a : ℕ × ℕ} : rel a a :=
!add.comm

theorem rel_symm {a b : ℕ × ℕ} (H : rel a b) : rel b a :=
calc
  pr1 b + pr2 a = pr2 a + pr1 b : !add.comm
    ... = pr1 a + pr2 b         : H⁻¹
    ... = pr2 b + pr1 a         : !add.comm

theorem rel_trans {a b c : ℕ × ℕ} (H1 : rel a b) (H2 : rel b c) : rel a c :=
have H3 : pr1 a + pr2 c + pr2 b = pr2 a + pr1 c + pr2 b, from
  calc
   pr1 a + pr2 c + pr2 b = pr1 a + pr2 b + pr2 c : by simp
    ... = pr2 a + pr1 b + pr2 c                  : {H1}
    ... = pr2 a + (pr1 b + pr2 c)                : by simp
    ... = pr2 a + (pr2 b + pr1 c)                : {H2}
    ... = pr2 a + pr1 c + pr2 b                  : by simp,
show pr1 a + pr2 c = pr2 a + pr1 c, from add.cancel_right H3

theorem rel_equiv : is_equivalence rel :=
is_equivalence.mk @rel_refl @rel_symm @rel_trans

theorem rel_flip {a b : ℕ × ℕ} (H : rel a b) : rel (flip a) (flip b) :=
calc
  pr1 (flip a) + pr2 (flip b) = pr2 a + pr1 b : by simp
    ... = pr1 a + pr2 b                       : H⁻¹
    ... = pr2 (flip a) + pr1 (flip b)         : by simp

-- ## The canonical representative of each equivalence class

definition proj (a : ℕ × ℕ) : ℕ × ℕ :=
if pr1 a ≥ pr2 a then pair (pr1 a - pr2 a) 0 else pair 0 (pr2 a - pr1 a)

theorem proj_ge {a : ℕ × ℕ} (H : pr1 a ≥ pr2 a) : proj a = pair (pr1 a - pr2 a) 0 :=
if_pos H

theorem proj_lt {a : ℕ × ℕ} (H : pr1 a < pr2 a) : proj a = pair 0 (pr2 a - pr1 a) :=
have H2 : ¬ pr1 a ≥ pr2 a, from lt_imp_not_ge H,
if_neg H2

theorem proj_le {a : ℕ × ℕ} (H : pr1 a ≤ pr2 a) : proj a = pair 0 (pr2 a - pr1 a) :=
or.elim le_or_gt
  (assume H2 : pr2 a ≤ pr1 a,
    have H3 : pr1 a = pr2 a, from le_antisym H H2,
    calc
      proj a = pair (pr1 a - pr2 a) 0 : proj_ge H2
        ... = pair (pr1 a - pr2 a) (pr1 a - pr1 a) : {!sub_self⁻¹}
        ... = pair (pr2 a - pr2 a) (pr2 a - pr1 a) : {H3}
        ... = pair 0 (pr2 a - pr1 a)               : {!sub_self})
  (assume H2 : pr1 a < pr2 a, proj_lt H2)

theorem proj_ge_pr1 {a : ℕ × ℕ} (H : pr1 a ≥ pr2 a) : pr1 (proj a) = pr1 a - pr2 a :=
calc
  pr1 (proj a) = pr1 (pair (pr1 a - pr2 a) 0) : {proj_ge H}
    ... = pr1 a - pr2 a : pr1.mk (pr1 a - pr2 a) 0

theorem proj_ge_pr2 {a : ℕ × ℕ} (H : pr1 a ≥ pr2 a) : pr2 (proj a) = 0 :=
calc
  pr2 (proj a) = pr2 (pair (pr1 a - pr2 a) 0) : {proj_ge H}
    ... = 0 : pr2.mk (pr1 a - pr2 a) 0

theorem proj_le_pr1 {a : ℕ × ℕ} (H : pr1 a ≤ pr2 a) : pr1 (proj a) = 0 :=
calc
  pr1 (proj a) = pr1 (pair 0 (pr2 a - pr1 a)) : {proj_le H}
    ... = 0 : pr1.mk 0 (pr2 a - pr1 a)

theorem proj_le_pr2 {a : ℕ × ℕ} (H : pr1 a ≤ pr2 a) : pr2 (proj a) = pr2 a - pr1 a :=
calc
  pr2 (proj a) = pr2 (pair 0 (pr2 a - pr1 a)) : {proj_le H}
    ... = pr2 a - pr1 a : pr2.mk 0 (pr2 a - pr1 a)

theorem proj_flip (a : ℕ × ℕ) : proj (flip a) = flip (proj a) :=
have special : ∀a, pr2 a ≤ pr1 a → proj (flip a) = flip (proj a), from
  take a,
  assume H : pr2 a ≤ pr1 a,
  have H2 : pr1 (flip a) ≤ pr2 (flip a), from P_flip a H,
  have H3 : pr1 (proj (flip a)) = pr1 (flip (proj a)), from
    calc
      pr1 (proj (flip a)) = 0 : proj_le_pr1 H2
        ... = pr2 (proj a) : (proj_ge_pr2 H)⁻¹
        ... = pr1 (flip (proj a)) : (flip_pr1 (proj a))⁻¹,
  have H4 : pr2 (proj (flip a)) = pr2 (flip (proj a)), from
    calc
      pr2 (proj (flip a)) = pr2 (flip a) - pr1 (flip a) : proj_le_pr2 H2
        ... = pr1 a - pr1 (flip a)                      : {flip_pr2 a}
        ... = pr1 a - pr2 a                             : {flip_pr1 a}
        ... = pr1 (proj a)                              : (proj_ge_pr1 H)⁻¹
        ... = pr2 (flip (proj a))                       : (flip_pr2 (proj a))⁻¹,
  prod.equal H3 H4,
or.elim !le_total
  (assume H : pr2 a ≤ pr1 a, special a H)
  (assume H : pr1 a ≤ pr2 a,
    have H2 : pr2 (flip a) ≤ pr1 (flip a), from P_flip a H,
    calc
      proj (flip a) = flip (flip (proj (flip a))) : (flip_flip (proj (flip a)))⁻¹
        ... = flip (proj (flip (flip a)))         : {(special (flip a) H2)⁻¹}
        ... = flip (proj a)                       : {flip_flip a})

theorem proj_rel (a : ℕ × ℕ) : rel a (proj a) :=
or.elim !le_total
  (assume H : pr2 a ≤ pr1 a,
    calc
      pr1 a + pr2 (proj a) = pr1 a + 0 : {proj_ge_pr2 H}
        ... = pr1 a                    : !add.zero_right
        ... = pr2 a + (pr1 a - pr2 a)  : (add_sub_le H)⁻¹
        ... = pr2 a + pr1 (proj a)     : {(proj_ge_pr1 H)⁻¹})
  (assume H : pr1 a ≤ pr2 a,
    calc
      pr1 a + pr2 (proj a) = pr1 a + (pr2 a - pr1 a) : {proj_le_pr2 H}
        ... = pr2 a                                  : add_sub_le H
        ... = pr2 a + 0                              : !add.zero_right⁻¹
        ... = pr2 a + pr1 (proj a)                   : {(proj_le_pr1 H)⁻¹})

theorem proj_congr {a b : ℕ × ℕ} (H : rel a b) : proj a = proj b :=
have special : ∀a b, pr2 a ≤ pr1 a → rel a b → proj a = proj b, from
  take a b,
  assume H2 : pr2 a ≤ pr1 a,
  assume H : rel a b,
  have H3 : pr1 a + pr2 b ≤ pr2 a + pr1 b, from H ▸ !le_refl,
  have H4 : pr2 b ≤ pr1 b, from add_le_inv H3 H2,
  have H5 : pr1 (proj a) = pr1 (proj b), from
    calc
      pr1 (proj a) = pr1 a - pr2 a          : proj_ge_pr1 H2
        ... = pr1 a + pr2 b - pr2 b - pr2 a : {!sub_add_left⁻¹}
        ... = pr2 a + pr1 b - pr2 b - pr2 a : {H}
        ... = pr2 a + pr1 b - pr2 a - pr2 b : {!sub_comm}
        ... = pr1 b - pr2 b                 : {!sub_add_left2}
        ... = pr1 (proj b)                  : (proj_ge_pr1 H4)⁻¹,
  have H6 : pr2 (proj a) = pr2 (proj b), from
    calc
      pr2 (proj a) = 0 : proj_ge_pr2 H2
        ... = pr2 (proj b) : {(proj_ge_pr2 H4)⁻¹},
  prod.equal H5 H6,
or.elim !le_total
  (assume H2 : pr2 a ≤ pr1 a, special a b H2 H)
  (assume H2 : pr1 a ≤ pr2 a,
    have H3 : pr2 (flip a) ≤ pr1 (flip a), from P_flip a H2,
    have H4 : proj (flip a) = proj (flip b), from special (flip a) (flip b) H3 (rel_flip H),
    have H5 : flip (proj a) = flip (proj b), from proj_flip a ▸ proj_flip b ▸ H4,
    show proj a = proj b, from flip_inj H5)

theorem proj_inj {a b : ℕ × ℕ} (H : proj a = proj b) : rel a b :=
representative_map_equiv_inj rel_equiv proj_rel @proj_congr H

theorem proj_zero_or (a : ℕ × ℕ) : pr1 (proj a) = 0 ∨ pr2 (proj a) = 0 :=
or.elim !le_total
  (assume H : pr2 a ≤ pr1 a, or.inr (proj_ge_pr2 H))
  (assume H : pr1 a ≤ pr2 a, or.inl (proj_le_pr1 H))

theorem proj_idempotent (a : ℕ × ℕ) : proj (proj a) = proj a :=
representative_map_idempotent_equiv proj_rel @proj_congr a

-- ## Definition of ℤ and basic theorems and definitions

protected opaque definition int := image proj
notation `ℤ` := int

opaque definition psub : ℕ × ℕ → ℤ := fun_image proj
opaque definition rep  : ℤ → ℕ × ℕ := subtype.elt_of

theorem quotient : is_quotient rel psub rep :=
representative_map_to_quotient_equiv rel_equiv proj_rel @proj_congr

theorem psub_rep (a : ℤ) : psub (rep a) = a :=
abs_rep quotient a

theorem destruct (a : ℤ) : ∃n m : ℕ, a = psub (pair n m) :=
exists_intro (pr1 (rep a))
  (exists_intro (pr2 (rep a))
    (calc
      a = psub (rep a) : (psub_rep a)⁻¹
    ... = psub (pair (pr1 (rep a)) (pr2 (rep a))) : {(prod.eta (rep a))⁻¹}))

-- TODO it should not be opaque.
protected opaque definition has_decidable_eq [instance] : decidable_eq ℤ :=
_

irreducible int
definition of_nat [coercion] [reducible] (n : ℕ) : ℤ := psub (pair n 0)
definition of_num [coercion] [reducible] (n : num) : ℤ := of_nat (nat.of_num n)

theorem eq_zero_intro (n : ℕ) : psub (pair n n) = 0 :=
have H : rel (pair n n) (pair 0 0), by simp,
eq_abs quotient H

definition to_nat : ℤ → ℕ := rec_constant quotient (fun v, dist (pr1 v) (pr2 v))

theorem to_nat_comp (n m : ℕ) : (to_nat (psub (pair n m))) = dist n m :=
have H : ∀v w : ℕ × ℕ, rel v w → dist (pr1 v) (pr2 v) = dist (pr1 w) (pr2 w),
  from take v w H, dist_eq_intro H,
have H2 : ∀v : ℕ × ℕ, (to_nat (psub v)) = dist (pr1 v) (pr2 v),
  from take v, (comp_constant quotient H rel_refl),
iff.mp (by simp) H2 (pair n m)

-- add_rewrite to_nat_comp --local

theorem to_nat_of_nat (n : ℕ) : to_nat (of_nat n) = n :=
calc
  (to_nat (psub (pair n 0))) = dist n 0 : by simp
    ... = n : by simp

theorem of_nat_inj {n m : ℕ} (H : of_nat n = of_nat m) : n = m :=
calc
  n = to_nat (of_nat n) : (to_nat_of_nat n)⁻¹
    ... = to_nat (of_nat m) : {H}
    ... = m : to_nat_of_nat m

theorem to_nat_eq_zero {a : ℤ} (H : to_nat a = 0) : a = 0 :=
obtain (xa ya : ℕ) (Ha : a = psub (pair xa ya)), from destruct a,
have H2 : dist xa ya = 0, from
  calc
    dist xa ya = (to_nat (psub (pair xa ya))) : by simp
      ... = (to_nat a) : {Ha⁻¹}
      ... = 0 : H,
have H3 : xa = ya, from dist_eq_zero H2,
calc
  a = psub (pair xa ya) : Ha
... = psub (pair ya ya) : {H3}
... = 0 : eq_zero_intro ya

-- add_rewrite to_nat_of_nat

-- ## neg

definition neg : ℤ → ℤ := quotient_map quotient flip

notation `-` x := neg x

theorem neg_comp (n m : ℕ) : -(psub (pair n m)) = psub (pair m n) :=
have H : ∀a, -(psub a) = psub (flip a),
  from take a, comp_quotient_map quotient @rel_flip rel_refl,
calc
  -(psub (pair n m)) = psub (flip (pair n m)) : H (pair n m)
    ... = psub (pair m n) : by simp

-- add_rewrite neg_comp --local

theorem neg_zero : -0 = 0 :=
calc -(psub (pair 0 0)) = psub (pair 0 0) : neg_comp 0 0

theorem neg_neg (a : ℤ) : -(-a) = a :=
obtain (xa ya : ℕ) (Ha : a = psub (pair xa ya)), from destruct a,
by simp

-- add_rewrite neg_neg neg_zero

theorem neg_inj {a b : ℤ} (H : -a = -b) : a = b :=
iff.mp (by simp) (congr_arg neg H)

theorem neg_move {a b : ℤ} (H : -a = b) : -b = a :=
H ▸ neg_neg a

theorem to_nat_neg (a : ℤ) : (to_nat (-a)) = (to_nat a) :=
obtain (xa ya : ℕ) (Ha : a = psub (pair xa ya)), from destruct a,
by simp

theorem pos_eq_neg {n m : ℕ} (H : n = -m) : n = 0 ∧ m = 0 :=
have H2 : ∀n : ℕ, n = psub (pair n 0), from take n : ℕ, rfl,
have H3 : psub (pair n 0) = psub (pair 0 m), from iff.mp (by simp) H,
have H4 : rel (pair n 0) (pair 0 m), from R_intro_refl quotient @rel_refl H3,
have H5 : n + m = 0, from
  calc
    n + m = pr1 (pair n 0) + pr2 (pair 0 m) : by simp
      ... = pr2 (pair n 0) + pr1 (pair 0 m) : H4
      ... = 0                               : by simp,
 add.eq_zero H5

-- add_rewrite to_nat_neg

---reverse equalities

reducible int

theorem cases (a : ℤ) : (∃n : ℕ, a = of_nat n) ∨ (∃n : ℕ, a = - n) :=
have Hrep : proj (rep a) = rep a, from @idempotent_image_fix _ proj proj_idempotent a,
or.imp_or (or.swap (proj_zero_or (rep a)))
  (assume H : pr2 (proj (rep a)) = 0,
    have H2 : pr2 (rep a) = 0, from Hrep ▸ H,
    exists_intro (pr1 (rep a))
      (calc
        a = psub (rep a) : (psub_rep a)⁻¹
          ... = psub (pair (pr1 (rep a)) (pr2 (rep a))) : {(prod.eta (rep a))⁻¹}
          ... = psub (pair (pr1 (rep a)) 0) : {H2}
          ... = of_nat (pr1 (rep a)) : rfl))
  (assume H : pr1 (proj (rep a)) = 0,
    have H2 : pr1 (rep a) = 0, from Hrep ▸ H,
    exists_intro (pr2 (rep a))
      (calc
        a = psub (rep a) : (psub_rep a)⁻¹
          ... = psub (pair (pr1 (rep a)) (pr2 (rep a))) : {(prod.eta (rep a))⁻¹}
          ... = psub (pair 0 (pr2 (rep a))) : {H2}
          ... = -(psub (pair (pr2 (rep a)) 0)) : by simp
          ... = -(of_nat (pr2 (rep a))) : rfl))

irreducible int

---rename to by_cases in Lean 0.2 (for now using this to avoid name clash)
theorem int_by_cases {P : ℤ → Prop} (a : ℤ) (H1 : ∀n : ℕ, P (of_nat n)) (H2 : ∀n : ℕ, P (-n)) :
  P a :=
or.elim (cases a)
  (assume H, obtain (n : ℕ) (H3 : a = n), from H, H3⁻¹ ▸ H1 n)
  (assume H, obtain (n : ℕ) (H3 : a = -n), from H, H3⁻¹ ▸ H2 n)

---reverse equalities, rename
theorem cases_succ (a : ℤ) : (∃n : ℕ, a = of_nat n) ∨ (∃n : ℕ, a = - (of_nat (succ n))) :=
or.elim (cases a)
  (assume H : (∃n : ℕ, a = of_nat n), or.inl H)
  (assume H,
    obtain (n : ℕ) (H2 : a = -(of_nat n)), from H,
    discriminate
      (assume H3 : n = 0,
        have H4 : a = of_nat 0, from
          calc
            a = -(of_nat n) : H2
          ... = -(of_nat 0) : {H3}
          ... = of_nat 0 : neg_zero,
        or.inl (exists_intro 0 H4))
      (take k : ℕ,
        assume H3 : n = succ k,
        have H4 : a = -(of_nat (succ k)), from H3 ▸ H2,
        or.inr (exists_intro k H4)))

theorem int_by_cases_succ {P : ℤ → Prop} (a : ℤ)
  (H1 : ∀n : ℕ, P (of_nat n)) (H2 : ∀n : ℕ, P (-(of_nat (succ n)))) : P a :=
or.elim (cases_succ a)
  (assume H, obtain (n : ℕ) (H3 : a = of_nat n), from H, H3⁻¹ ▸ H1 n)
  (assume H, obtain (n : ℕ) (H3 : a = -(of_nat (succ n))), from H, H3⁻¹ ▸ H2 n)

--some of these had to be transparent for theorem cases
irreducible psub proj

-- ## add

theorem rel_add {a a' b b' : ℕ × ℕ} (Ha : rel a a') (Hb : rel b b')
  : rel (map_pair2 add a b) (map_pair2 add a' b') :=
calc
  pr1 (map_pair2 add a b) + pr2 (map_pair2 add a' b')  = pr1 a + pr2 a' + (pr1 b + pr2 b') : by simp
    ... = pr2 a + pr1 a' + (pr1 b + pr2 b') : {Ha}
    ... = pr2 a + pr1 a' + (pr2 b + pr1 b') : {Hb}
    ... = pr2 (map_pair2 add a b) + pr1 (map_pair2 add a' b') : by simp

definition add : ℤ → ℤ → ℤ := quotient_map_binary quotient (map_pair2 nat.add)
notation a + b := int.add a b

theorem add_comp (n m k l : ℕ) : psub (pair n m) + psub (pair k l) = psub (pair (n + k) (m + l)) :=
have H : ∀a b, psub a + psub b = psub (map_pair2 nat.add a b),
  from comp_quotient_map_binary_refl @rel_refl quotient @rel_add,
H (pair n m) (pair k l) ⬝ by simp

-- add_rewrite add_comp --local

theorem add_comm (a b : ℤ) : a + b = b + a :=
obtain (xa ya : ℕ) (Ha : a = psub (pair xa ya)), from destruct a,
obtain (xb yb : ℕ) (Hb : b = psub (pair xb yb)), from destruct b,
by simp

theorem add_assoc (a b c : ℤ) : a + b + c = a + (b + c) :=
obtain (xa ya : ℕ) (Ha : a = psub (pair xa ya)), from destruct a,
obtain (xb yb : ℕ) (Hb : b = psub (pair xb yb)), from destruct b,
obtain (xc yc : ℕ) (Hc : c = psub (pair xc yc)), from destruct c,
by simp

theorem add_left_comm (a b c : ℤ) : a + (b + c) = b + (a + c) :=
left_comm add_comm add_assoc a b c

theorem add_right_comm (a b c : ℤ) : a + b + c = a + c + b :=
right_comm add_comm add_assoc a b c

-- ### interaction of add with other functions and constants

theorem add_zero_right (a : ℤ) : a + 0 = a :=
obtain (xa ya : ℕ) (Ha : a = psub (pair xa ya)), from destruct a,
have H0 : 0 = psub (pair 0 0), from rfl,
by simp

theorem add_zero_left (a : ℤ) : 0 + a = a :=
add_comm a 0 ▸ add_zero_right a

theorem add_inverse_right (a : ℤ) : a + -a = 0 :=
have H : ∀n, psub (pair n n) = 0, from eq_zero_intro,
obtain (xa ya : ℕ) (Ha : a = psub (pair xa ya)), from destruct a,
by simp

theorem add_inverse_left (a : ℤ) : -a + a = 0 :=
add_comm a (-a) ▸ add_inverse_right a

theorem neg_add_distr (a b : ℤ) : -(a + b) = -a + -b :=
obtain (xa ya : ℕ) (Ha : a = psub (pair xa ya)), from destruct a,
obtain (xb yb : ℕ) (Hb : b = psub (pair xb yb)), from destruct b,
by simp

theorem to_nat_add_le (a b : ℤ) : to_nat (a + b) ≤ to_nat a + to_nat b :=
  --note: ≤ is nat::≤
obtain (xa ya : ℕ) (Ha : a = psub (pair xa ya)), from destruct a,
obtain (xb yb : ℕ) (Hb : b = psub (pair xb yb)), from destruct b,
have H : dist (xa + xb) (ya + yb) ≤ dist xa ya + dist xb yb,
  from !dist_add_le_add_dist,
by simp

-- TODO: note, we have to add #nat to get the right interpretation
theorem add_of_nat (n m : nat) : of_nat n + of_nat m = #nat n + m := -- this is of_nat (n + m)
have H : ∀n : ℕ, n = psub (pair n 0), from take n : ℕ, rfl,
by simp

-- add_rewrite add_of_nat

theorem of_nat_succ (n : ℕ) : of_nat (succ n) = of_nat n + 1 :=
by simp

-- ## sub
definition sub (a b : ℤ) : ℤ := a + -b
notation a - b := int.sub a b

theorem sub_def (a b : ℤ) : a - b = a + -b :=
rfl

theorem add_neg_right (a b : ℤ) : a + -b = a - b :=
rfl

theorem add_neg_left (a b : ℤ) : -a + b = b - a :=
add_comm (-a) b

theorem sub_neg_right (a b : ℤ) : a - (-b) = a + b :=
neg_neg b ▸ eq.refl (a - (-b))

theorem sub_neg_neg (a b : ℤ) : -a - (-b) = b - a :=
neg_neg b ▸ add_comm (-a) (-(-b))

theorem sub_self (a : ℤ) : a - a = 0 :=
add_inverse_right a

theorem sub_zero_right (a : ℤ) : a - 0 = a :=
neg_zero⁻¹ ▸ add_zero_right a

theorem sub_zero_left (a : ℤ) : 0 - a = -a :=
add_zero_left (-a)

theorem neg_sub  (a b : ℤ) : -(a - b) = -a + b :=
calc
  -(a - b) = -a + -(-b) : neg_add_distr a (-b)
    ... = -a + b : {neg_neg b}

theorem neg_sub_flip (a b : ℤ) : -(a - b) = b - a :=
calc
  -(a - b) = -a + b : neg_sub a b
    ... = b - a : add_comm (-a) b

theorem sub_sub_assoc (a b c : ℤ) : a - b - c = a - (b + c) :=
calc
  a - b - c = a + (-b + -c) : add_assoc a (-b) (-c)
    ... = a + -(b + c) : {(neg_add_distr b c)⁻¹}

theorem sub_add_assoc (a b c : ℤ) : a - b + c = a - (b - c) :=
calc
  a - b + c = a + (-b + c) : add_assoc a (-b) c
    ... = a + -(b - c) : {(neg_sub b c)⁻¹}

theorem add_sub_assoc (a b c : ℤ) : a + b - c = a + (b - c) :=
add_assoc a b (-c)

theorem add_sub_inverse (a b : ℤ) : a + b - b = a :=
calc
  a + b - b = a + (b - b) : add_assoc a b (-b)
    ... = a + 0 : {sub_self b}
    ... = a : add_zero_right a

theorem add_sub_inverse2 (a b : ℤ) : a + b - a = b :=
add_comm b a ▸ add_sub_inverse b a

theorem sub_add_inverse (a b : ℤ) : a - b + b = a :=
add_right_comm a b (-b) ▸ add_sub_inverse a b

-- add_rewrite add_zero_left add_zero_right
-- add_rewrite add_comm add_assoc add_left_comm
-- add_rewrite sub_def add_inverse_right add_inverse_left
-- add_rewrite neg_add_distr
---- add_rewrite sub_sub_assoc sub_add_assoc add_sub_assoc
---- add_rewrite add_neg_right add_neg_left
---- add_rewrite sub_self

-- ### inversion theorems for add and sub

-- a + a = 0 -> a = 0
-- a = -a -> a = 0

theorem add_cancel_right {a b c : ℤ} (H : a + c = b + c) : a = b :=
calc
  a = a + c - c : (add_sub_inverse a c)⁻¹
... = b + c - c : {H}
... = b : add_sub_inverse b c

theorem add_cancel_left {a b c : ℤ} (H : a + b = a + c) : b = c :=
add_cancel_right ((H ▸ (add_comm a b)) ▸ add_comm a c)

theorem add_eq_zero_right {a b : ℤ} (H : a + b = 0) : -a = b :=
have H2 : a + -a = a + b, from (add_inverse_right a)⁻¹ ▸ H⁻¹,
show -a = b, from add_cancel_left H2

theorem add_eq_zero_left {a b : ℤ} (H : a + b = 0) : -b = a :=
neg_move (add_eq_zero_right H)

theorem add_eq_self {a b : ℤ} (H : a + b = a) : b = 0 :=
add_cancel_left (H ⬝ (add_zero_right a)⁻¹)

theorem sub_inj_left {a b c : ℤ} (H : a - b = a - c) : b = c :=
neg_inj (add_cancel_left H)

theorem sub_inj_right {a b c : ℤ} (H : a - b = c - b) : a = c :=
add_cancel_right H

theorem sub_eq_zero {a b : ℤ} (H : a - b = 0) : a = b :=
neg_inj (add_eq_zero_right H)

theorem add_imp_sub_right {a b c : ℤ} (H : a + b = c) : c - b = a :=
have H2 : c - b + b = a + b, from (sub_add_inverse c b) ⬝ H⁻¹,
add_cancel_right H2

theorem add_imp_sub_left {a b c : ℤ} (H : a + b = c) : c - a = b :=
add_imp_sub_right (add_comm a b ▸ H)

theorem sub_imp_add {a b c : ℤ} (H : a - b = c) : c + b = a :=
neg_neg b ▸ add_imp_sub_right H

theorem sub_imp_sub {a b c : ℤ} (H : a - b = c) : a - c = b :=
have H2 : c + b = a, from sub_imp_add H, add_imp_sub_left H2

theorem sub_add_add_right (a b c : ℤ) : a + c - (b + c) = a - b :=
calc
  a + c - (b + c) = a + (c - (b + c)) : add_sub_assoc a c (b + c)
    ... = a + (c - b - c) : {(sub_sub_assoc c b c)⁻¹}
    ... = a + -b : {add_sub_inverse2 c (-b)}

theorem sub_add_add_left (a b c : ℤ) : c + a - (c + b) = a - b :=
add_comm b c ▸ add_comm a c ▸ sub_add_add_right a b c

theorem dist_def (n m : ℕ) : dist n m = (to_nat (of_nat n - m)) :=
have H : of_nat n - m = psub (pair n m), from
  calc
    psub (pair n 0) + -psub (pair m 0) = psub (pair (n + 0) (0 + m)) : by simp
      ... = psub (pair n m) : by simp,
calc
  dist n m = (to_nat (psub (pair n m))) : by simp
    ... = (to_nat (of_nat n - m)) : {H⁻¹}

-- ## mul
theorem rel_mul_prep {xa ya xb yb xn yn xm ym : ℕ}
  (H1 : xa + yb = ya + xb) (H2 : xn + ym = yn + xm)
: xa * xn + ya * yn + (xb * ym + yb * xm) = xa * yn + ya * xn + (xb * xm + yb * ym) :=
have H3 : xa * xn + ya * yn + (xb * ym + yb * xm) + (yb * xn + xb * yn + (xb * xn + yb * yn))
    = xa * yn + ya * xn + (xb * xm + yb * ym) + (yb * xn + xb * yn + (xb * xn + yb * yn)), from
  calc
    xa * xn + ya * yn + (xb * ym + yb * xm) + (yb * xn + xb * yn + (xb * xn + yb * yn))
          = xa * xn + yb * xn + (ya * yn + xb * yn) + (xb * xn + xb * ym + (yb * yn + yb * xm))
            : by simp
      ... = (xa + yb) * xn + (ya + xb) * yn + (xb * (xn + ym) + yb * (yn + xm)) : by simp
      ... = (ya + xb) * xn + (xa + yb) * yn + (xb * (yn + xm) + yb * (xn + ym)) : by simp
      ... = ya * xn + xb * xn + (xa * yn + yb * yn) + (xb * yn + xb * xm + (yb*xn + yb*ym))
            : by simp
      ... = xa * yn + ya * xn + (xb * xm + yb * ym) + (yb * xn + xb * yn + (xb * xn + yb * yn))
            : by simp,
nat.add.cancel_right H3

theorem rel_mul {u u' v v' : ℕ × ℕ} (H1 : rel u u') (H2 : rel v v') :
  rel (pair (pr1 u * pr1 v + pr2 u * pr2 v) (pr1 u * pr2 v + pr2 u * pr1 v))
        (pair (pr1 u' * pr1 v' + pr2 u' * pr2 v') (pr1 u' * pr2 v' + pr2 u' * pr1 v')) :=
calc
    pr1 (pair (pr1 u * pr1 v + pr2 u * pr2 v) (pr1 u * pr2 v + pr2 u * pr1 v))
  + pr2 (pair (pr1 u' * pr1 v' + pr2 u' * pr2 v') (pr1 u' * pr2 v' + pr2 u' * pr1 v'))
  = (pr1 u * pr1 v + pr2 u * pr2 v) + (pr1 u' * pr2 v' + pr2 u' * pr1 v') : by simp
... = (pr1 u * pr2 v + pr2 u * pr1 v) + (pr1 u' * pr1 v' + pr2 u' * pr2 v') : rel_mul_prep H1 H2
... = pr2 (pair (pr1 u * pr1 v + pr2 u * pr2 v) (pr1 u * pr2 v + pr2 u * pr1 v))
  + pr1 (pair (pr1 u' * pr1 v' + pr2 u' * pr2 v') (pr1 u' * pr2 v' + pr2 u' * pr1 v')) : by simp

definition mul : ℤ → ℤ → ℤ := quotient_map_binary quotient
  (fun u v : ℕ × ℕ, pair (pr1 u * pr1 v + pr2 u * pr2 v) (pr1 u * pr2 v + pr2 u * pr1 v))

notation a * b := int.mul a b

theorem mul_comp (n m k l : ℕ) :
  psub (pair n m) * psub (pair k l) = psub (pair (n * k + m * l) (n * l + m * k)) :=
have H : ∀u v,
    psub u * psub v = psub (pair (pr1 u * pr1 v + pr2 u * pr2 v) (pr1 u * pr2 v + pr2 u * pr1 v)),
  from comp_quotient_map_binary_refl @rel_refl quotient @rel_mul,
H (pair n m) (pair k l) ⬝ by simp

-- add_rewrite mul_comp

theorem mul_comm (a b : ℤ) : a * b = b * a :=
obtain (xa ya : ℕ) (Ha : a = psub (pair xa ya)), from destruct a,
obtain (xb yb : ℕ) (Hb : b = psub (pair xb yb)), from destruct b,
by simp

theorem mul_assoc (a b c : ℤ) : (a * b) * c = a * (b * c) :=
obtain (xa ya : ℕ) (Ha : a = psub (pair xa ya)), from destruct a,
obtain (xb yb : ℕ) (Hb : b = psub (pair xb yb)), from destruct b,
obtain (xc yc : ℕ) (Hc : c = psub (pair xc yc)), from destruct c,
by simp

theorem mul_left_comm : ∀a b c : ℤ, a * (b * c) = b * (a * c) :=
left_comm mul_comm mul_assoc

theorem mul_right_comm : ∀a b c : ℤ, a * b * c = a * c * b :=
right_comm mul_comm mul_assoc

-- ### interaction with other objects

theorem mul_zero_right (a : ℤ) : a * 0 = 0 :=
obtain (xa ya : ℕ) (Ha : a = psub (pair xa ya)), from destruct a,
have H0 : 0 = psub (pair 0 0), from rfl,
by simp

theorem mul_zero_left (a : ℤ) : 0 * a = 0 :=
mul_comm a 0 ▸ mul_zero_right a

theorem mul_one_right (a : ℤ) : a * 1 = a :=
obtain (xa ya : ℕ) (Ha : a = psub (pair xa ya)), from destruct a,
have H1 : 1 = psub (pair 1 0), from rfl,
by simp

theorem mul_one_left (a : ℤ) : 1 * a = a :=
mul_comm a 1 ▸ mul_one_right a

theorem mul_neg_right (a b : ℤ) : a * -b = -(a * b) :=
obtain (xa ya : ℕ) (Ha : a = psub (pair xa ya)), from destruct a,
obtain (xb yb : ℕ) (Hb : b = psub (pair xb yb)), from destruct b,
by simp

theorem mul_neg_left (a b : ℤ) : -a * b = -(a * b) :=
mul_comm b a ▸ mul_comm b (-a) ▸ mul_neg_right b a

-- add_rewrite mul_neg_right mul_neg_left

theorem mul_neg_neg (a b : ℤ) : -a * -b = a * b :=
by simp

theorem mul_right_distr (a b c : ℤ) : (a + b) * c = a * c + b * c :=
obtain (xa ya : ℕ) (Ha : a = psub (pair xa ya)), from destruct a,
obtain (xb yb : ℕ) (Hb : b = psub (pair xb yb)), from destruct b,
obtain (xc yc : ℕ) (Hc : c = psub (pair xc yc)), from destruct c,
by simp

theorem mul_left_distr (a b c : ℤ) : a * (b + c) = a * b + a * c :=
calc
  a * (b + c) = (b + c) * a : mul_comm a (b + c)
    ... = b * a + c * a : mul_right_distr b c a
    ... = a * b + c * a : {mul_comm b a}
    ... = a * b + a * c : {mul_comm c a}

theorem mul_sub_right_distr (a b c : ℤ) : (a - b) * c = a * c - b * c :=
calc
  (a + -b) * c = a * c + -b * c : mul_right_distr a (-b) c
    ... = a * c + - (b * c) : {mul_neg_left b c}

theorem mul_sub_left_distr (a b c : ℤ) : a * (b - c) = a * b - a * c :=
calc
  a * (b + -c) = a * b + a * -c : mul_left_distr a b (-c)
    ... = a * b + - (a * c) : {mul_neg_right a c}

theorem mul_of_nat (n m : ℕ) : of_nat n * of_nat m = n * m :=
have H : ∀n : ℕ, n = psub (pair n 0), from take n : ℕ, rfl,
by simp

theorem mul_to_nat (a b : ℤ) : (to_nat (a * b)) = #nat (to_nat a) * (to_nat b) :=
obtain (xa ya : ℕ) (Ha : a = psub (pair xa ya)), from destruct a,
obtain (xb yb : ℕ) (Hb : b = psub (pair xb yb)), from destruct b,
have H : dist xa ya * dist xb yb = dist (xa * xb + ya * yb) (xa * yb + ya * xb),
  from !dist_mul_dist,
by simp

-- add_rewrite mul_zero_left mul_zero_right mul_one_right mul_one_left
-- add_rewrite mul_comm mul_assoc mul_left_comm
-- add_rewrite mul_distr_right mul_distr_left mul_of_nat mul_sub_distr_left mul_sub_distr_right


-- ---------- inversion

theorem mul_eq_zero {a b : ℤ} (H : a * b = 0) : a = 0 ∨ b = 0 :=
have H2 : (to_nat a) * (to_nat b) = 0, from
  calc
    (to_nat a) * (to_nat b) = (to_nat (a * b)) : (mul_to_nat a b)⁻¹
      ... = (to_nat 0) : {H}
      ... = 0 : to_nat_of_nat 0,
have H3 : (to_nat a) = 0 ∨ (to_nat b) = 0, from mul.eq_zero H2,
or.imp_or H3
  (assume H : (to_nat a) = 0, to_nat_eq_zero H)
  (assume H : (to_nat b) = 0, to_nat_eq_zero H)

theorem mul_cancel_left_or {a b c : ℤ} (H : a * b = a * c) : a = 0 ∨ b = c :=
have H2 : a * (b - c) = 0, by simp,
have H3 : a = 0 ∨ b - c = 0, from mul_eq_zero H2,
or.imp_or_right H3 (assume H4 : b - c = 0, sub_eq_zero H4)

theorem mul_cancel_left {a b c : ℤ} (H1 : a ≠ 0) (H2 : a * b = a * c) : b = c :=
or.resolve_right (mul_cancel_left_or H2) H1

theorem mul_cancel_right_or {a b c : ℤ} (H : b * a = c * a) : a = 0 ∨ b = c :=
mul_cancel_left_or ((H ▸ (mul_comm b a)) ▸ mul_comm c a)

theorem mul_cancel_right {a b c : ℤ} (H1 : c ≠ 0) (H2 : a * c = b * c) : a = b :=
or.resolve_right (mul_cancel_right_or H2) H1

theorem mul_ne_zero {a b : ℤ} (Ha : a ≠ 0) (Hb : b ≠ 0) : a * b ≠ 0 :=
not_intro
  (assume H : a * b = 0,
    or.elim (mul_eq_zero H)
      (assume H2 : a = 0, absurd H2 Ha)
      (assume H2 : b = 0, absurd H2 Hb))

theorem mul_ne_zero_left {a b : ℤ} (H : a * b ≠ 0) : a ≠ 0 :=
not_intro
  (assume H2 : a = 0,
    have H3 : a * b = 0, by simp,
    absurd H3 H)

theorem mul_ne_zero_right {a b : ℤ} (H : a * b ≠ 0) : b ≠ 0 :=
mul_ne_zero_left (mul_comm a b ▸ H)

end int
definition int := int.int
