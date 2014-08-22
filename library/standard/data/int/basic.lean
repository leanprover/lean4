-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Floris van Doorn

-- Theory int
-- ==========

import ..nat.basic ..nat.order ..nat.sub ..prod ..quotient ..quotient tools.tactic struc.relation
import struc.binary

import tools.fake_simplifier

namespace int
using nat (hiding case)
using quotient
using subtype
using prod
using relation
using decidable
using binary

using fake_simplifier


-- ## The defining equivalence relation on ℕ × ℕ

abbreviation rel (a b : ℕ × ℕ) : Prop :=  pr1 a + pr2 b = pr2 a + pr1 b

theorem rel_comp (n m k l : ℕ) : (rel (pair n m) (pair k l)) ↔ (n + l = m + k) :=
have H : (pr1 (pair n m) + pr2 (pair k l) = pr2 (pair n m) + pr1 (pair k l)) ↔ (n + l = m + k),
  by simp,
H

-- add_rewrite rel_comp --local

theorem rel_refl (a : ℕ × ℕ) : rel a a :=
add_comm (pr1 a) (pr2 a)

theorem rel_symm {a b : ℕ × ℕ} (H : rel a b) : rel b a :=
calc
  pr1 b + pr2 a = pr2 a + pr1 b : add_comm _ _
    ... = pr1 a + pr2 b : symm H
    ... = pr2 b + pr1 a : add_comm _ _

theorem rel_trans {a b c : ℕ × ℕ} (H1 : rel a b) (H2 : rel b c) : rel a c :=
have H3 : pr1 a + pr2 c + pr2 b = pr2 a + pr1 c + pr2 b, from
  calc
   pr1 a + pr2 c + pr2 b = pr1 a + pr2 b + pr2 c : by simp
    ... = pr2 a + pr1 b + pr2 c : {H1}
    ... = pr2 a + (pr1 b + pr2 c) : by simp
    ... = pr2 a + (pr2 b + pr1 c) : {H2}
    ... = pr2 a + pr1 c + pr2 b : by simp,
show pr1 a + pr2 c = pr2 a + pr1 c, from add_cancel_right H3

theorem rel_equiv : is_equivalence rel :=
is_equivalence_mk (is_reflexive_mk rel_refl) (is_symmetric_mk @rel_symm)
(is_transitive_mk @rel_trans)

theorem rel_flip {a b : ℕ × ℕ} (H : rel a b) : rel (flip a) (flip b) :=
calc
  pr1 (flip a) + pr2 (flip b) = pr2 a + pr1 b : by simp
    ... = pr1 a + pr2 b : symm H
    ... = pr2 (flip a) + pr1 (flip b) : by simp

-- ## The canonical representative of each equivalence class

definition proj (a : ℕ × ℕ) : ℕ × ℕ :=
if pr1 a ≥ pr2 a then pair (pr1 a - pr2 a) 0 else pair 0 (pr2 a - pr1 a)

theorem proj_ge {a : ℕ × ℕ} (H : pr1 a ≥ pr2 a) : proj a = pair (pr1 a - pr2 a) 0 :=
if_pos H _ _

theorem proj_lt {a : ℕ × ℕ} (H : pr1 a < pr2 a) : proj a = pair 0 (pr2 a - pr1 a) :=
have H2 : ¬ pr1 a ≥ pr2 a, from lt_imp_not_ge H,
if_neg H2 _ _

theorem proj_le {a : ℕ × ℕ} (H : pr1 a ≤ pr2 a) : proj a = pair 0 (pr2 a - pr1 a) :=
or_elim (le_or_gt (pr2 a) (pr1 a))
  (assume H2 : pr2 a ≤ pr1 a,
    have H3 : pr1 a = pr2 a, from le_antisym H H2,
    calc
      proj a = pair (pr1 a - pr2 a) 0 : proj_ge H2
        ... = pair (pr1 a - pr2 a) (pr1 a - pr1 a) : {symm (sub_self (pr1 a))}
        ... = pair (pr2 a - pr2 a) (pr2 a - pr1 a) : {H3}
        ... = pair 0 (pr2 a - pr1 a) : {sub_self (pr2 a)})
  (assume H2 : pr1 a < pr2 a, proj_lt H2)

theorem proj_ge_pr1 {a : ℕ × ℕ} (H : pr1 a ≥ pr2 a) : pr1 (proj a) = pr1 a - pr2 a :=
calc
  pr1 (proj a) = pr1 (pair (pr1 a - pr2 a) 0) : {proj_ge H}
    ... = pr1 a - pr2 a : pr1_pair (pr1 a - pr2 a) 0

theorem proj_ge_pr2 {a : ℕ × ℕ} (H : pr1 a ≥ pr2 a) : pr2 (proj a) = 0 :=
calc
  pr2 (proj a) = pr2 (pair (pr1 a - pr2 a) 0) : {proj_ge H}
    ... = 0 : pr2_pair (pr1 a - pr2 a) 0

theorem proj_le_pr1 {a : ℕ × ℕ} (H : pr1 a ≤ pr2 a) : pr1 (proj a) = 0 :=
calc
  pr1 (proj a) = pr1 (pair 0 (pr2 a - pr1 a)) : {proj_le H}
    ... = 0 : pr1_pair 0 (pr2 a - pr1 a)

theorem proj_le_pr2 {a : ℕ × ℕ} (H : pr1 a ≤ pr2 a) : pr2 (proj a) = pr2 a - pr1 a :=
calc
  pr2 (proj a) = pr2 (pair 0 (pr2 a - pr1 a)) : {proj_le H}
    ... = pr2 a - pr1 a : pr2_pair 0 (pr2 a - pr1 a)

theorem proj_flip (a : ℕ × ℕ) : proj (flip a) = flip (proj a) :=
have special : ∀a, pr2 a ≤ pr1 a → proj (flip a) = flip (proj a), from
  take a,
  assume H : pr2 a ≤ pr1 a,
  have H2 : pr1 (flip a) ≤ pr2 (flip a), from P_flip H,
  have H3 : pr1 (proj (flip a)) = pr1 (flip (proj a)), from
    calc
      pr1 (proj (flip a)) = 0 : proj_le_pr1 H2
        ... = pr2 (proj a) : symm (proj_ge_pr2 H)
        ... = pr1 (flip (proj a)) : symm (flip_pr1 (proj a)),
  have H4 : pr2 (proj (flip a)) = pr2 (flip (proj a)), from
    calc
      pr2 (proj (flip a)) = pr2 (flip a) - pr1 (flip a) : proj_le_pr2 H2
        ... = pr1 a - pr1 (flip a) : {flip_pr2 a}
        ... = pr1 a - pr2 a : {flip_pr1 a}
        ... = pr1 (proj a) : symm (proj_ge_pr1 H)
        ... = pr2 (flip (proj a)) : symm (flip_pr2 (proj a)),
  prod_eq H3 H4,
or_elim (le_total (pr2 a) (pr1 a))
  (assume H : pr2 a ≤ pr1 a, special a H)
  (assume H : pr1 a ≤ pr2 a,
    have H2 : pr2 (flip a) ≤ pr1 (flip a), from P_flip H,
    calc
      proj (flip a) = flip (flip (proj (flip a))) : symm (flip_flip (proj (flip a)))
        ... = flip (proj (flip (flip a))) : {symm (special (flip a) H2)}
        ... = flip (proj a) : {flip_flip a})

theorem proj_rel (a : ℕ × ℕ) : rel a (proj a) :=
or_elim (le_total (pr2 a) (pr1 a))
  (assume H : pr2 a ≤ pr1 a,
    calc
      pr1 a + pr2 (proj a) = pr1 a + 0 : {proj_ge_pr2 H}
        ... = pr1 a : add_zero_right (pr1 a)
        ... = pr2 a + (pr1 a - pr2 a) : symm (add_sub_le H)
        ... = pr2 a + pr1 (proj a) : {symm (proj_ge_pr1 H)})
  (assume H : pr1 a ≤ pr2 a,
    calc
      pr1 a + pr2 (proj a) = pr1 a + (pr2 a - pr1 a) : {proj_le_pr2 H}
        ... = pr2 a : add_sub_le H
        ... = pr2 a + 0 : symm (add_zero_right (pr2 a))
        ... = pr2 a + pr1 (proj a) : {symm (proj_le_pr1 H)})

theorem proj_congr {a b : ℕ × ℕ} (H : rel a b) : proj a = proj b :=
have special : ∀a b, pr2 a ≤ pr1 a → rel a b → proj a = proj b, from
  take a b,
  assume H2 : pr2 a ≤ pr1 a,
  assume H : rel a b,
  have H3 : pr1 a + pr2 b ≤ pr2 a + pr1 b, from subst H (le_refl (pr1 a + pr2 b)),
  have H4 : pr2 b ≤ pr1 b, from add_le_inv H3 H2,
  have H5 : pr1 (proj a) = pr1 (proj b), from
    calc
      pr1 (proj a) = pr1 a - pr2 a : proj_ge_pr1 H2
        ... = pr1 a + pr2 b - pr2 b - pr2 a : {symm (sub_add_left (pr1 a) (pr2 b))}
        ... = pr2 a + pr1 b - pr2 b - pr2 a : {H}
        ... = pr2 a + pr1 b - pr2 a - pr2 b : {sub_comm _ _ _}
        ... = pr1 b - pr2 b : {sub_add_left2 (pr2 a) (pr1 b)}
        ... = pr1 (proj b) : symm (proj_ge_pr1 H4),
  have H6 : pr2 (proj a) = pr2 (proj b), from
    calc
      pr2 (proj a) = 0 : proj_ge_pr2 H2
        ... = pr2 (proj b) : {symm (proj_ge_pr2 H4)},
  prod_eq H5 H6,
or_elim (le_total (pr2 a) (pr1 a))
  (assume H2 : pr2 a ≤ pr1 a, special a b H2 H)
  (assume H2 : pr1 a ≤ pr2 a,
    have H3 : pr2 (flip a) ≤ pr1 (flip a), from P_flip H2,
    have H4 : proj (flip a) = proj (flip b), from special (flip a) (flip b) H3 (rel_flip H),
    have H5 : flip (proj a) = flip (proj b), from subst (proj_flip a) (subst (proj_flip b) H4),
    show proj a = proj b, from flip_inj H5)

theorem proj_inj {a b : ℕ × ℕ} (H : proj a = proj b) : rel a b :=
representative_map_equiv_inj rel_equiv proj_rel @proj_congr H

theorem proj_zero_or (a : ℕ × ℕ) : pr1 (proj a) = 0 ∨ pr2 (proj a) = 0 :=
or_elim (le_total (pr2 a) (pr1 a))
  (assume H : pr2 a ≤ pr1 a, or_intro_right _ (proj_ge_pr2 H))
  (assume H : pr1 a ≤ pr2 a, or_intro_left _ (proj_le_pr1 H))

theorem proj_idempotent (a : ℕ × ℕ) : proj (proj a) = proj a :=
representative_map_idempotent_equiv proj_rel @proj_congr a

-- ## Definition of ℤ and basic theorems and definitions

definition int := image proj
notation `ℤ`:max := int

definition psub : ℕ × ℕ → ℤ := fun_image proj
definition rep : ℤ → ℕ × ℕ := subtype.elt_of

theorem quotient : is_quotient rel psub rep :=
representative_map_to_quotient_equiv rel_equiv proj_rel @proj_congr

theorem psub_rep (a : ℤ) : psub (rep a) = a :=
abs_rep quotient a

theorem destruct (a : ℤ) : ∃n m : ℕ, a = psub (pair n m) :=
exists_intro (pr1 (rep a))
  (exists_intro (pr2 (rep a))
    (calc
      a = psub (rep a) : symm (psub_rep a)
    ... = psub (pair (pr1 (rep a)) (pr2 (rep a))) : {symm (prod_ext (rep a))}))

definition of_nat (n : ℕ) : ℤ := psub (pair n 0)

theorem int_eq_decidable [instance] (a b : ℤ) : decidable (a = b) := _
-- subtype_eq_decidable _ _ (prod_eq_decidable _ _ _ _)

opaque_hint (hiding int)
coercion of_nat

theorem eq_zero_intro (n : ℕ) : psub (pair n n) = 0 :=
have H : rel (pair n n) (pair 0 0), by simp,
eq_abs quotient H

definition to_nat : ℤ → ℕ := rec_constant quotient (fun v, dist (pr1 v) (pr2 v))

-- TODO: set binding strength: is this right?
notation `|`:40 x:40 `|` := to_nat x

theorem to_nat_comp (n m : ℕ) : (to_nat (psub (pair n m))) = dist n m :=
have H : ∀v w : ℕ × ℕ, rel v w → dist (pr1 v) (pr2 v) = dist (pr1 w) (pr2 w),
  from take v w H, dist_eq_intro H,
have H2 : ∀v : ℕ × ℕ, (to_nat (psub v)) = dist (pr1 v) (pr2 v),
  from take v, (comp_constant quotient H (rel_refl v)),
(by simp) ◂ H2 (pair n m)

-- add_rewrite to_nat_comp --local

theorem to_nat_of_nat (n : ℕ) : to_nat (of_nat n) = n :=
calc
  (to_nat (psub (pair n 0))) = dist n 0 : by simp
    ... = n : by simp

theorem of_nat_inj {n m : ℕ} (H : of_nat n = of_nat m) : n = m :=
calc
  n = to_nat (of_nat n) : symm (to_nat_of_nat n)
    ... = to_nat (of_nat m) : {H}
    ... = m : to_nat_of_nat m

theorem to_nat_eq_zero {a : ℤ} (H : to_nat a = 0) : a = 0 :=
obtain (xa ya : ℕ) (Ha : a = psub (pair xa ya)), from destruct a,
have H2 : dist xa ya = 0, from
  calc
    dist xa ya = (to_nat (psub (pair xa ya))) : by simp
      ... = (to_nat a) : {symm Ha}
      ... = 0 : H,
have H3 : xa = ya, from dist_eq_zero H2,
calc
  a = psub (pair xa ya) : Ha
... = psub (pair ya ya) : {H3}
... = 0 : eq_zero_intro ya

-- add_rewrite to_nat_of_nat

-- ## neg

definition neg : ℤ → ℤ := quotient_map quotient flip

-- TODO: is this good?
prefix `-`:80 := neg

theorem neg_comp (n m : ℕ) : -psub (pair n m) = psub (pair m n) :=
have H : ∀a, -psub a = psub (flip a),
  from take a, comp_quotient_map quotient @rel_flip (rel_refl _),
calc
  -psub (pair n m) = psub (flip (pair n m)) : H (pair n m)
    ... = psub (pair m n) : by simp

-- add_rewrite neg_comp --local

theorem neg_zero : -0 = 0 :=
calc -psub (pair 0 0) = psub (pair 0 0) : neg_comp 0 0

theorem neg_neg (a : ℤ) : -(-a) = a :=
obtain (xa ya : ℕ) (Ha : a = psub (pair xa ya)), from destruct a,
by simp

-- add_rewrite neg_neg neg_zero

theorem neg_inj {a b : ℤ} (H : -a = -b) : a = b :=
(by simp) ◂ congr_arg neg H

theorem neg_move {a b : ℤ} (H : -a = b) : -b = a :=
subst H (neg_neg a)

theorem to_nat_neg (a : ℤ) : (to_nat (-a)) = (to_nat a) :=
obtain (xa ya : ℕ) (Ha : a = psub (pair xa ya)), from destruct a,
by simp

theorem pos_eq_neg {n m : ℕ} (H : n = -m) : n = 0 ∧ m = 0 :=
have H2 : ∀n : ℕ, n = psub (pair n 0), from take n : ℕ, refl (n),
have H3 : psub (pair n 0) = psub (pair 0 m), from (by simp) ◂ H,
have H4 : rel (pair n 0) (pair 0 m), from R_intro_refl quotient rel_refl H3,
have H5 : n + m = 0, from
  calc
    n + m = pr1 (pair n 0) + pr2 (pair 0 m) : by simp
      ... = pr2 (pair n 0) + pr1 (pair 0 m) : H4
      ... = 0 : by simp,
 add_eq_zero H5

-- add_rewrite to_nat_neg

---reverse equalities

opaque_hint (exposing int)

theorem cases (a : ℤ) : (∃n : ℕ, a = of_nat n) ∨ (∃n : ℕ, a = - n) :=
have Hrep : proj (rep a) = rep a, from @idempotent_image_fix _ proj proj_idempotent a,
or_imp_or (or_swap (proj_zero_or (rep a)))
  (assume H : pr2 (proj (rep a)) = 0,
    have H2 : pr2 (rep a) = 0, from subst Hrep H,
    exists_intro (pr1 (rep a))
      (calc
        a = psub (rep a) : symm (psub_rep a)
          ... = psub (pair (pr1 (rep a)) (pr2 (rep a))) : {symm (prod_ext (rep a))}
          ... = psub (pair (pr1 (rep a)) 0) : {H2}
          ... = of_nat (pr1 (rep a)) : refl _))
  (assume H : pr1 (proj (rep a)) = 0,
    have H2 : pr1 (rep a) = 0, from subst Hrep H,
    exists_intro (pr2 (rep a))
      (calc
        a = psub (rep a) : symm (psub_rep a)
          ... = psub (pair (pr1 (rep a)) (pr2 (rep a))) : {symm (prod_ext (rep a))}
          ... = psub (pair 0 (pr2 (rep a))) : {H2}
          ... = -psub (pair (pr2 (rep a)) 0) : by simp
          ... = -of_nat (pr2 (rep a)) : refl _))

opaque_hint (hiding int)

---rename to by_cases in Lean 0.2 (for now using this to avoid name clash)
theorem int_by_cases {P : ℤ → Prop} (a : ℤ) (H1 : ∀n : ℕ, P (of_nat n)) (H2 : ∀n : ℕ, P (-n)) :
  P a :=
or_elim (cases a)
  (assume H, obtain (n : ℕ) (H3 : a = n), from H, subst (symm H3) (H1 n))
  (assume H, obtain (n : ℕ) (H3 : a = -n), from H, subst (symm H3) (H2 n))

---reverse equalities, rename
theorem cases_succ (a : ℤ) : (∃n : ℕ, a = of_nat n) ∨ (∃n : ℕ, a = - of_nat (succ n)) :=
or_elim (cases a)
  (assume H : (∃n : ℕ, a = of_nat n), or_intro_left _ H)
  (assume H,
    obtain (n : ℕ) (H2 : a = -of_nat n), from H,
    discriminate
      (assume H3 : n = 0,
        have H4 : a = of_nat 0, from
          calc
            a = - of_nat n : H2
          ... = - of_nat 0 : {H3}
          ... = of_nat 0 : neg_zero,
        or_intro_left _ (exists_intro 0 H4))
      (take k : ℕ,
        assume H3 : n = succ k,
        have H4 : a = - of_nat (succ k), from subst H3 H2,
        or_intro_right _ (exists_intro k H4)))

theorem int_by_cases_succ {P : ℤ → Prop} (a : ℤ)
  (H1 : ∀n : ℕ, P (of_nat n)) (H2 : ∀n : ℕ, P (-of_nat (succ n))) : P a :=
or_elim (cases_succ a)
  (assume H, obtain (n : ℕ) (H3 : a = of_nat n), from H, subst (symm H3) (H1 n))
  (assume H, obtain (n : ℕ) (H3 : a = -of_nat (succ n)), from H, subst (symm H3) (H2 n))

theorem of_nat_eq_neg_of_nat {n m : ℕ} (H : n = - m) : n = 0 ∧ m = 0 :=
have H2 : n = psub (pair 0 m), from
  calc
    n = -m : H
      ... = -psub (pair m 0) : refl (-m)
      ... = psub (pair 0 m) : by simp,
have H3 : rel (pair n 0) (pair 0 m), from R_intro_refl quotient rel_refl H2,
have H4 : n + m = 0, from
  calc
    n + m = pr1 (pair n 0) + pr2 (pair 0 m) : by simp
      ... = pr2 (pair n 0) + pr1 (pair 0 m) : H3
      ... = 0 : by simp,
add_eq_zero H4

--some of these had to be transparent for theorem cases
opaque_hint (hiding psub proj)

-- ## add

theorem rel_add {a a' b b' : ℕ × ℕ} (Ha : rel a a') (Hb : rel b b')
  : rel (map_pair2 add a b) (map_pair2 add a' b') :=
calc
  pr1 (map_pair2 add a b) + pr2 (map_pair2 add a' b')  = pr1 a + pr2 a' + (pr1 b + pr2 b') : by simp
    ... = pr2 a + pr1 a' + (pr1 b + pr2 b') : {Ha}
    ... = pr2 a + pr1 a' + (pr2 b + pr1 b') : {Hb}
    ... = pr2 (map_pair2 add a b) + pr1 (map_pair2 add a' b') : by simp

definition add : ℤ → ℤ → ℤ := quotient_map_binary quotient (map_pair2 nat.add)
infixl `+` := int.add

theorem add_comp (n m k l : ℕ) : psub (pair n m) + psub (pair k l) = psub (pair (n + k) (m + l)) :=
have H : ∀a b, psub a + psub b = psub (map_pair2 nat.add a b),
  from comp_quotient_map_binary_refl rel_refl quotient @rel_add,
trans (H (pair n m) (pair k l)) (by simp)

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
have H0 : 0 = psub (pair 0 0), from refl 0,
by simp

theorem add_zero_left (a : ℤ) : 0 + a = a :=
subst (add_comm a 0) (add_zero_right a)

theorem add_inverse_right (a : ℤ) : a + -a = 0 :=
have H : ∀n, psub (pair n n) = 0, from eq_zero_intro,
obtain (xa ya : ℕ) (Ha : a = psub (pair xa ya)), from destruct a,
by simp

theorem add_inverse_left (a : ℤ) : -a + a = 0 :=
subst (add_comm a (-a)) (add_inverse_right a)

theorem neg_add_distr (a b : ℤ) : -(a + b) = -a + -b :=
obtain (xa ya : ℕ) (Ha : a = psub (pair xa ya)), from destruct a,
obtain (xb yb : ℕ) (Hb : b = psub (pair xb yb)), from destruct b,
by simp

theorem to_nat_add_le (a b : ℤ) : to_nat (a + b) ≤ to_nat a + to_nat b :=
  --note: ≤ is nat::≤
obtain (xa ya : ℕ) (Ha : a = psub (pair xa ya)), from destruct a,
obtain (xb yb : ℕ) (Hb : b = psub (pair xb yb)), from destruct b,
have H : dist (xa + xb) (ya + yb) ≤ dist xa ya + dist xb yb,
  from dist_add_le_add_dist xa xb ya yb,
by simp

-- TODO: add this to eq
-- notation A `=` B `:` C := @eq C A B

-- TODO: note, we have to add #nat to get the right interpretation
theorem add_of_nat (n m : nat) : of_nat n + of_nat m = #nat n + m := -- this is of_nat (n + m)
have H : ∀n : ℕ, n = psub (pair n 0), from take n : ℕ, refl n,
by simp

-- add_rewrite add_of_nat

theorem of_nat_succ (n : ℕ) : of_nat (succ n) = of_nat n + 1 :=
by simp

-- ## sub
definition sub (a b : ℤ) : ℤ := a + -b
infixl `-`:65 := int.sub

theorem sub_def (a b : ℤ) : a - b = a + -b :=
refl (a - b)

theorem add_neg_right (a b : ℤ) : a + -b = a - b :=
refl (a - b)

theorem add_neg_left (a b : ℤ) : -a + b = b - a :=
add_comm (-a) b

-- opaque_hint (hiding int.sub)

theorem sub_neg_right (a b : ℤ) : a - (-b) = a + b :=
subst (neg_neg b) (refl (a - (-b)))

theorem sub_neg_neg (a b : ℤ) : -a - (-b) = b - a :=
subst (neg_neg b) (add_comm (-a) (-(-b)))

theorem sub_self (a : ℤ) : a - a = 0 :=
add_inverse_right a

theorem sub_zero_right (a : ℤ) : a - 0 = a :=
subst (symm neg_zero) (add_zero_right a)

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
    ... = a + -(b + c) : {symm (neg_add_distr b c)}

theorem sub_add_assoc (a b c : ℤ) : a - b + c = a - (b - c) :=
calc
  a - b + c = a + (-b + c) : add_assoc a (-b) c
    ... = a + -(b - c) : {symm (neg_sub b c)}

theorem add_sub_assoc (a b c : ℤ) : a + b - c = a + (b - c) :=
add_assoc a b (-c)

theorem add_sub_inverse (a b : ℤ) : a + b - b = a :=
calc
  a + b - b = a + (b - b) : add_assoc a b (-b)
    ... = a + 0 : {sub_self b}
    ... = a : add_zero_right a

theorem add_sub_inverse2 (a b : ℤ) : a + b - a = b :=
subst (add_comm b a) (add_sub_inverse b a)

theorem sub_add_inverse (a b : ℤ) : a - b + b = a :=
subst (add_right_comm a b (-b)) (add_sub_inverse a b)

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
  a = a + c - c : symm (add_sub_inverse a c)
... = b + c - c : {H}
... = b : add_sub_inverse b c

theorem add_cancel_left {a b c : ℤ} (H : a + b = a + c) : b = c :=
add_cancel_right (subst (subst H (add_comm a b)) (add_comm a c))

theorem add_eq_zero_right {a b : ℤ} (H : a + b = 0) : -a = b :=
have H2 : a + -a = a + b, from subst (symm (add_inverse_right a)) (symm H),
show -a = b, from add_cancel_left H2

theorem add_eq_zero_left {a b : ℤ} (H : a + b = 0) : -b = a :=
neg_move (add_eq_zero_right H)

theorem add_eq_self {a b : ℤ} (H : a + b = a) : b = 0 :=
add_cancel_left (trans H (symm (add_zero_right a)))

theorem sub_inj_left {a b c : ℤ} (H : a - b = a - c) : b = c :=
neg_inj (add_cancel_left H)

theorem sub_inj_right {a b c : ℤ} (H : a - b = c - b) : a = c :=
add_cancel_right H

theorem sub_eq_zero {a b : ℤ} (H : a - b = 0) : a = b :=
neg_inj (add_eq_zero_right H)

theorem add_imp_sub_right {a b c : ℤ} (H : a + b = c) : c - b = a :=
have H2 : c - b + b = a + b, from trans (sub_add_inverse c b) (symm H),
add_cancel_right H2

theorem add_imp_sub_left {a b c : ℤ} (H : a + b = c) : c - a = b :=
add_imp_sub_right (subst (add_comm a b) H)

theorem sub_imp_add {a b c : ℤ} (H : a - b = c) : c + b = a :=
subst (neg_neg b) (add_imp_sub_right H)

theorem sub_imp_sub {a b c : ℤ} (H : a - b = c) : a - c = b :=
have H2 : c + b = a, from sub_imp_add H, add_imp_sub_left H2

theorem sub_add_add_right (a b c : ℤ) : a + c - (b + c) = a - b :=
calc
  a + c - (b + c) = a + (c - (b + c)) : add_sub_assoc a c (b + c)
    ... = a + (c - b - c) : {symm (sub_sub_assoc c b c)}
    ... = a + -b : {add_sub_inverse2 c (-b)}

theorem sub_add_add_left (a b c : ℤ) : c + a - (c + b) = a - b :=
subst (add_comm b c) (subst (add_comm a c) (sub_add_add_right a b c))

-- TODO: fix this
theorem dist_def (n m : ℕ) : dist n m = (to_nat (of_nat n - m)) :=
have H [fact] : of_nat n - m = psub (pair n m), from
  calc
    psub (pair n 0) + -psub (pair m 0) = psub (pair (n + 0) (0 + m)) : by simp
      ... = psub (pair n m) : by simp,
calc
  dist n m = (to_nat (psub (pair n m))) : by simp
    ... = (to_nat (of_nat n - m)) : sorry -- {symm H}

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
nat.add_cancel_right H3

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

infixl `*` := int.mul

theorem mul_comp (n m k l : ℕ) :
  psub (pair n m) * psub (pair k l) = psub (pair (n * k + m * l) (n * l + m * k)) :=
have H : ∀u v,
    psub u * psub v = psub (pair (pr1 u * pr1 v + pr2 u * pr2 v) (pr1 u * pr2 v + pr2 u * pr1 v)),
  from comp_quotient_map_binary_refl rel_refl quotient @rel_mul,
trans (H (pair n m) (pair k l)) (by simp)

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
have H0 : 0 = psub (pair 0 0), from refl 0,
by simp

theorem mul_zero_left (a : ℤ) : 0 * a = 0 :=
subst (mul_comm a 0) (mul_zero_right a)

theorem mul_one_right (a : ℤ) : a * 1 = a :=
obtain (xa ya : ℕ) (Ha : a = psub (pair xa ya)), from destruct a,
have H1 : 1 = psub (pair 1 0), from refl 1,
by simp

theorem mul_one_left (a : ℤ) : 1 * a = a :=
subst (mul_comm a 1) (mul_one_right a)

theorem mul_neg_right (a b : ℤ) : a * -b = -(a * b) :=
obtain (xa ya : ℕ) (Ha : a = psub (pair xa ya)), from destruct a,
obtain (xb yb : ℕ) (Hb : b = psub (pair xb yb)), from destruct b,
by simp

theorem mul_neg_left (a b : ℤ) : -a * b = -(a * b) :=
subst (mul_comm b a) (subst (mul_comm b (-a)) (mul_neg_right b a))

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
have H : ∀n : ℕ, n = psub (pair n 0), from take n : ℕ, refl n,
by simp

theorem mul_to_nat (a b : ℤ) : (to_nat (a * b)) = #nat (to_nat a) * (to_nat b) :=
obtain (xa ya : ℕ) (Ha : a = psub (pair xa ya)), from destruct a,
obtain (xb yb : ℕ) (Hb : b = psub (pair xb yb)), from destruct b,
have H : dist xa ya * dist xb yb = dist (xa * xb + ya * yb) (xa * yb + ya * xb),
  from dist_mul_dist xa ya xb yb,
by simp

-- add_rewrite mul_zero_left mul_zero_right mul_one_right mul_one_left
-- add_rewrite mul_comm mul_assoc mul_left_comm
-- add_rewrite mul_distr_right mul_distr_left mul_of_nat mul_sub_distr_left mul_sub_distr_right


-- ---------- inversion

theorem mul_eq_zero {a b : ℤ} (H : a * b = 0) : a = 0 ∨ b = 0 :=
have H2 : (to_nat a) * (to_nat b) = 0, from
  calc
    (to_nat a) * (to_nat b) = (to_nat (a * b)) : symm (mul_to_nat a b)
      ... = (to_nat 0) : {H}
      ... = 0 : to_nat_of_nat 0,
have H3 : (to_nat a) = 0 ∨ (to_nat b) = 0, from mul_eq_zero H2,
or_imp_or H3
  (assume H : (to_nat a) = 0, to_nat_eq_zero H)
  (assume H : (to_nat b) = 0, to_nat_eq_zero H)

theorem mul_cancel_left_or {a b c : ℤ} (H : a * b = a * c) : a = 0 ∨ b = c :=
have H2 : a * (b - c) = 0, by simp,
have H3 : a = 0 ∨ b - c = 0, from mul_eq_zero H2,
or_imp_or_right H3 (assume H4 : b - c = 0, sub_eq_zero H4)

theorem mul_cancel_left {a b c : ℤ} (H1 : a ≠ 0) (H2 : a * b = a * c) : b = c :=
resolve_right (mul_cancel_left_or H2) H1

theorem mul_cancel_right_or {a b c : ℤ} (H : b * a = c * a) : a = 0 ∨ b = c :=
mul_cancel_left_or (subst (subst H (mul_comm b a)) (mul_comm c a))

theorem mul_cancel_right {a b c : ℤ} (H1 : c ≠ 0) (H2 : a * c = b * c) : a = b :=
resolve_right (mul_cancel_right_or H2) H1

theorem mul_ne_zero {a b : ℤ} (Ha : a ≠ 0) (Hb : b ≠ 0) : a * b ≠ 0 :=
not_intro
  (assume H : a * b = 0,
    or_elim (mul_eq_zero H)
      (assume H2 : a = 0, absurd H2 Ha)
      (assume H2 : b = 0, absurd H2 Hb))

theorem mul_ne_zero_left {a b : ℤ} (H : a * b ≠ 0) : a ≠ 0 :=
not_intro
  (assume H2 : a = 0,
    have H3 : a * b = 0, by simp,
    absurd H3 H)

theorem mul_ne_zero_right {a b : ℤ} (H : a * b ≠ 0) : b ≠ 0 :=
mul_ne_zero_left (subst (mul_comm a b) H)

-- ## le
definition le (a b : ℤ) : Prop := ∃n : ℕ, a + n = b
infix  `<=` := int.le
infix  `≤`  := int.le

theorem le_intro {a b : ℤ} {n : ℕ} (H : a + n = b) : a ≤ b :=
exists_intro n H

theorem le_elim {a b : ℤ} (H : a ≤ b) : ∃n : ℕ, a + n = b :=
H

-- ### partial order

theorem le_refl (a : ℤ) : a ≤ a :=
le_intro (add_zero_right a)

theorem le_of_nat (n m : ℕ) : (of_nat n ≤ of_nat m) ↔ (n ≤ m) :=
iff_intro
  (assume H : of_nat n ≤ of_nat m,
    obtain (k : ℕ) (Hk : of_nat n + of_nat k = of_nat m), from le_elim H,
    have H2 : n + k = m, from of_nat_inj (trans (symm (add_of_nat n k)) Hk),
    nat.le_intro H2)
  (assume H : n ≤ m,
    obtain (k : ℕ) (Hk : n + k = m), from nat.le_elim H,
    have H2 : of_nat n + of_nat k = of_nat m, from subst Hk (add_of_nat n k),
    le_intro H2)

theorem le_trans {a b c : ℤ} (H1 : a ≤ b) (H2 : b ≤ c) : a ≤ c :=
obtain (n : ℕ) (Hn : a + n = b), from le_elim H1,
obtain (m : ℕ) (Hm : b + m = c), from le_elim H2,
have H3 : a + of_nat (n + m) = c, from
  calc
    a + of_nat (n + m) = a + (of_nat n + m) : {symm (add_of_nat n m)}
      ... = a + n + m : symm (add_assoc a n m)
      ... = b + m : {Hn}
      ... = c : Hm,
le_intro H3

theorem le_antisym {a b : ℤ} (H1 : a ≤ b) (H2 : b ≤ a) : a = b :=
obtain (n : ℕ) (Hn : a + n = b), from le_elim H1,
obtain (m : ℕ) (Hm : b + m = a), from le_elim H2,
have H3 : a + of_nat (n + m) = a + 0, from
  calc
    a + of_nat (n + m) = a + (of_nat n + m) : {symm (add_of_nat n m)}
      ... = a + n + m : symm (add_assoc a n m)
      ... = b + m : {Hn}
      ... = a : Hm
      ... = a + 0 : symm (add_zero_right a),
have H4 : of_nat (n + m) = of_nat 0, from add_cancel_left H3,
have H5 : n + m = 0, from of_nat_inj H4,
have H6 : n = 0, from nat.add_eq_zero_left H5,
show a = b, from
  calc
    a = a + of_nat 0 : symm (add_zero_right a)
      ... = a + n : {symm H6}
      ... = b : Hn

-- ### interaction with add

theorem le_add_of_nat_right (a : ℤ) (n : ℕ) : a ≤ a + n :=
le_intro (refl (a + n))

theorem le_add_of_nat_left (a : ℤ) (n : ℕ) : a ≤ n + a :=
le_intro (add_comm a n)

theorem add_le_left {a b : ℤ} (H : a ≤ b) (c : ℤ) : c + a ≤ c + b :=
obtain (n : ℕ) (Hn : a + n = b), from le_elim H,
have H2 : c + a + n = c + b, from
  calc
    c + a + n = c + (a + n) : add_assoc c a n
      ... = c + b : {Hn},
le_intro H2

theorem add_le_right {a b : ℤ} (H : a ≤ b) (c : ℤ) : a + c ≤ b + c :=
subst (add_comm c b) (subst (add_comm c a) (add_le_left H c))

theorem add_le {a b c d : ℤ} (H1 : a ≤ b) (H2 : c ≤ d) : a + c ≤ b + d :=
le_trans (add_le_right H1 c) (add_le_left H2 b)

theorem add_le_cancel_right {a b c : ℤ} (H : a + c ≤ b + c) : a ≤ b :=
have H2 : a + c - c ≤ b + c - c, from add_le_right H (-c),
subst (add_sub_inverse b c) (subst (add_sub_inverse a c) H2)

theorem add_le_cancel_left {a b c : ℤ} (H : c + a ≤ c + b) : a ≤ b :=
add_le_cancel_right (subst (add_comm c b) (subst (add_comm c a) H))

theorem add_le_inv {a b c d : ℤ} (H1 : a + b ≤ c + d) (H2 : c ≤ a) : b ≤ d :=
obtain (n : ℕ) (Hn : c + n = a), from le_elim H2,
have H3 : c + (n + b) ≤ c + d, from subst (add_assoc c n b) (subst (symm Hn) H1),
have H4 : n + b ≤ d, from add_le_cancel_left H3,
show b ≤ d, from le_trans (le_add_of_nat_left b n) H4

theorem le_add_of_nat_right_trans {a b : ℤ} (H : a ≤ b) (n : ℕ) : a ≤ b + n :=
le_trans H (le_add_of_nat_right b n)

theorem le_imp_succ_le_or_eq {a b : ℤ} (H : a ≤ b) : a + 1 ≤ b ∨ a = b :=
obtain (n : ℕ) (Hn : a + n = b), from le_elim H,
discriminate
  (assume H2 : n = 0,
    have H3 : a = b, from
      calc
        a = a + 0 : symm (add_zero_right a)
          ... = a + n : {symm H2}
          ... = b : Hn,
    or_intro_right _ H3)
  (take k : ℕ,
    assume H2 : n = succ k,
    have H3 : a + 1 + k = b, from
      calc
        a + 1 + k = a + succ k : by simp
          ... = a + n : by simp
          ... = b : Hn,
    or_intro_left _ (le_intro H3))

-- ### interaction with neg and sub

theorem le_neg {a b : ℤ} (H : a ≤ b) : -b ≤ -a :=
obtain (n : ℕ) (Hn : a + n = b), from le_elim H,
have H2 : b - n = a, from add_imp_sub_right Hn,
have H3 : -b + n = -a, from
  calc
    -b + n = -b + -(-n) : {symm (neg_neg n)}
      ... = -(b - n) : symm (neg_add_distr b (-n))
      ... = -a : {H2},
le_intro H3

theorem neg_le_zero {a : ℤ} (H : 0 ≤ a) : -a ≤ 0 :=
subst neg_zero (le_neg H)

theorem zero_le_neg {a : ℤ} (H : a ≤ 0) : 0 ≤ -a :=
subst neg_zero (le_neg H)

theorem le_neg_inv {a b : ℤ} (H : -a ≤ -b) : b ≤ a :=
subst (neg_neg b) (subst (neg_neg a) (le_neg H))

theorem le_sub_of_nat (a : ℤ) (n : ℕ) : a - n ≤ a :=
le_intro (sub_add_inverse a n)

theorem sub_le_right {a b : ℤ} (H : a ≤ b) (c : ℤ) : a - c ≤ b - c :=
add_le_right H (-c)

theorem sub_le_left {a b : ℤ} (H : a ≤ b) (c : ℤ) : c - b ≤ c - a :=
add_le_left (le_neg H) c

theorem sub_le {a b c d : ℤ} (H1 : a ≤ b) (H2 : d ≤ c) : a - c ≤ b - d :=
add_le H1 (le_neg H2)

theorem sub_le_right_inv {a b c : ℤ} (H : a - c ≤ b - c) : a ≤ b :=
add_le_cancel_right H

theorem sub_le_left_inv {a b c : ℤ} (H : c - a ≤ c - b) : b ≤ a :=
le_neg_inv (add_le_cancel_left H)

theorem le_iff_sub_nonneg (a b : ℤ) : a ≤ b ↔ 0 ≤ b - a :=
iff_intro
  (assume H, subst (sub_self _) (sub_le_right H a))
  (assume H, subst (sub_add_inverse _ _) (subst (add_zero_left _) (add_le_right H a)))


-- Less than, Greater than, Greater than or equal
-- ----------------------------------------------

definition lt (a b : ℤ) := a + 1 ≤ b
infix `<` := int.lt

definition ge (a b : ℤ) := b ≤ a
infix `>=` := int.ge
infix `≥`  := int.ge

definition gt (a b : ℤ) := b < a
infix `>` := int.gt

theorem lt_def (a b : ℤ) : a < b ↔ a + 1 ≤ b :=
iff_refl (a < b)

theorem gt_def (n m : ℕ) : n > m ↔ m < n :=
iff_refl (n > m)

theorem ge_def (n m : ℕ) : n ≥ m ↔ m ≤ n :=
iff_refl (n ≥ m)

-- add_rewrite gt_def ge_def --it might be possible to remove this in Lean 0.2

theorem lt_add_succ (a : ℤ) (n : ℕ) : a < a + succ n :=
le_intro (show a + 1 + n = a + succ n, by simp)

theorem lt_intro {a b : ℤ} {n : ℕ} (H : a + succ n = b) : a < b :=
subst H (lt_add_succ a n)

theorem lt_elim {a b : ℤ} (H : a < b) : ∃n : ℕ, a + succ n = b :=
obtain (n : ℕ) (Hn : a + 1 + n = b), from le_elim H,
have H2 : a + succ n = b, from
  calc
    a + succ n = a + 1 + n : by simp
      ... = b : Hn,
exists_intro n H2

-- -- ### basic facts

theorem lt_irrefl (a : ℤ) : ¬ a < a :=
not_intro
  (assume H : a < a,
    obtain (n : ℕ) (Hn : a + succ n = a), from lt_elim H,
    have H2 : a + succ n = a + 0, from
      calc
        a + succ n = a : Hn
          ... = a + 0 : by simp,
    have H3 : succ n = 0, from add_cancel_left H2,
    have H4 : succ n = 0, from of_nat_inj H3,
    absurd H4 (succ_ne_zero n))

theorem lt_imp_ne {a b : ℤ} (H : a < b) : a ≠ b :=
not_intro (assume H2 : a = b, absurd (subst H2 H) (lt_irrefl b))

theorem lt_of_nat (n m : ℕ) : (of_nat n < of_nat m) ↔ (n < m) :=
calc
  (of_nat n + 1 ≤ of_nat m) ↔ (of_nat (succ n) ≤ of_nat m) : by simp
    ... ↔ (succ n ≤ m) : le_of_nat (succ n) m
    ... ↔ (n < m) : iff_symm (eq_to_iff (nat.lt_def n m))

theorem gt_of_nat (n m : ℕ) : (of_nat n > of_nat m) ↔ (n > m) :=
lt_of_nat m n

-- ### interaction with le

theorem lt_imp_le_succ {a b : ℤ} (H : a < b) : a + 1 ≤ b :=
H

theorem le_succ_imp_lt {a b : ℤ} (H : a + 1 ≤ b) : a < b :=
H

theorem self_lt_succ (a : ℤ) : a < a + 1 :=
le_refl (a + 1)

theorem lt_imp_le {a b : ℤ} (H : a < b) : a ≤ b :=
obtain (n : ℕ) (Hn : a + succ n = b), from lt_elim H,
le_intro Hn

theorem le_imp_lt_or_eq {a b : ℤ} (H : a ≤ b) : a < b ∨ a = b :=
le_imp_succ_le_or_eq H

theorem le_ne_imp_lt {a b : ℤ} (H1 : a ≤ b)  (H2 : a ≠ b) : a < b :=
resolve_left (le_imp_lt_or_eq H1) H2

theorem le_imp_lt_succ {a b : ℤ} (H : a ≤ b) : a < b + 1 :=
add_le_right H 1

theorem lt_succ_imp_le {a b : ℤ} (H : a < b + 1) : a ≤ b :=
add_le_cancel_right H


-- ### transitivity, antisymmmetry

theorem lt_le_trans {a b c : ℤ} (H1 : a < b) (H2 : b ≤ c) : a < c :=
le_trans H1 H2

theorem le_lt_trans {a b c : ℤ} (H1 : a ≤ b) (H2 : b < c) : a < c :=
le_trans (add_le_right H1 1) H2

theorem lt_trans {a b c : ℤ} (H1 : a < b) (H2 : b < c) : a < c :=
lt_le_trans H1 (lt_imp_le H2)

theorem le_imp_not_gt {a b : ℤ} (H : a ≤ b) : ¬ a > b :=
not_intro (assume H2 : a > b, absurd (le_lt_trans H H2) (lt_irrefl a))

theorem lt_imp_not_ge {a b : ℤ} (H : a < b) : ¬ a ≥ b :=
not_intro (assume H2 : a ≥ b, absurd (lt_le_trans H H2) (lt_irrefl a))

theorem lt_antisym {a b : ℤ} (H : a < b) : ¬ b < a :=
le_imp_not_gt (lt_imp_le H)

-- ### interaction with addition

theorem add_lt_left {a b : ℤ} (H : a < b) (c : ℤ) : c + a < c + b :=
subst (symm (add_assoc c a 1)) (add_le_left H c)

theorem add_lt_right {a b : ℤ} (H : a < b) (c : ℤ) : a + c < b + c :=
subst (add_comm c b) (subst (add_comm c a) (add_lt_left H c))

theorem add_le_lt {a b c d : ℤ} (H1 : a ≤ c) (H2 : b < d) : a + b < c + d :=
le_lt_trans (add_le_right H1 b) (add_lt_left H2 c)

theorem add_lt_le {a b c d : ℤ} (H1 : a < c) (H2 : b ≤ d) : a + b < c + d :=
lt_le_trans (add_lt_right H1 b) (add_le_left H2 c)

theorem add_lt {a b c d : ℤ} (H1 : a < c) (H2 : b < d) : a + b < c + d :=
add_lt_le H1 (lt_imp_le H2)

theorem add_lt_cancel_left {a b c : ℤ} (H : c + a < c + b) : a < b :=
add_le_cancel_left (subst (add_assoc c a 1) (show c + a + 1 ≤ c + b, from H))

theorem add_lt_cancel_right {a b c : ℤ} (H : a + c < b + c) : a < b :=
add_lt_cancel_left (subst (add_comm b c) (subst (add_comm a c) H))


-- ### interaction with neg and sub

theorem lt_neg {a b : ℤ} (H : a < b) : -b < -a :=
have H2 : -(a + 1) + 1 = -a, by simp,
have H3 : -b ≤ -(a + 1), from le_neg H,
have H4 : -b + 1 ≤ -(a + 1) + 1, from add_le_right H3 1,
subst H2 H4

theorem neg_lt_zero {a : ℤ} (H : 0 < a) : -a < 0 :=
subst neg_zero (lt_neg H)

theorem zero_lt_neg {a : ℤ} (H : a < 0) : 0 < -a :=
subst neg_zero (lt_neg H)

theorem lt_neg_inv {a b : ℤ} (H : -a < -b) : b < a :=
subst (neg_neg b) (subst (neg_neg a) (lt_neg H))

theorem lt_sub_of_nat_succ (a : ℤ) (n : ℕ) : a - succ n < a :=
lt_intro (sub_add_inverse a (succ n))

theorem sub_lt_right {a b : ℤ} (H : a < b) (c : ℤ) : a - c < b - c :=
add_lt_right H (-c)

theorem sub_lt_left {a b : ℤ} (H : a < b) (c : ℤ) : c - b < c - a :=
add_lt_left (lt_neg H) c

theorem sub_lt {a b c d : ℤ} (H1 : a < b) (H2 : d < c) : a - c < b - d :=
add_lt H1 (lt_neg H2)

theorem sub_lt_right_inv {a b c : ℤ} (H : a - c < b - c) : a < b :=
add_lt_cancel_right H

theorem sub_lt_left_inv {a b c : ℤ} (H : c - a < c - b) : b < a :=
lt_neg_inv (add_lt_cancel_left H)

-- ### totality of lt and le

-- add_rewrite succ_pos zero_le --move some of these to nat.lean
-- add_rewrite le_of_nat lt_of_nat gt_of_nat --remove gt_of_nat in Lean 0.2
-- add_rewrite le_neg lt_neg neg_le_zero zero_le_neg zero_lt_neg neg_lt_zero

-- axiom sorry {P : Prop} : P

theorem neg_le_pos (n m : ℕ) : -n ≤ m :=
have H1 : of_nat 0 ≤ of_nat m, by simp,
have H2 : -n ≤ 0, by simp,
le_trans H2 H1

theorem le_or_gt (a b : ℤ) : a ≤ b ∨ a > b :=
int_by_cases a
  (take n : ℕ,
    int_by_cases_succ b
      (take m : ℕ,
        show of_nat n ≤ m ∨ of_nat n > m, by simp) -- from (by simp) ◂ (le_or_gt n m))
      (take m : ℕ,
        show n ≤ -succ m ∨ n > -succ m, from
          have H0 : -succ m < -m, from lt_neg (subst (symm (of_nat_succ m)) (self_lt_succ m)),
          have H : -succ m < n, from lt_le_trans H0 (neg_le_pos m n),
          or_intro_right _ H))
  (take n : ℕ,
    int_by_cases_succ b
      (take m : ℕ,
        show -n ≤ m ∨ -n > m, from
          or_intro_left _ (neg_le_pos n m))
      (take m : ℕ,
        show -n ≤ -succ m ∨ -n > -succ m, from
          or_imp_or (le_or_gt (succ m) n)
            (assume H : succ m ≤ n,
              le_neg (iff_elim_left (iff_symm (le_of_nat (succ m) n)) H))
            (assume H : succ m > n,
              lt_neg (iff_elim_left (iff_symm (lt_of_nat n (succ m))) H))))

theorem trichotomy_alt (a b : ℤ) : (a < b ∨ a = b) ∨ a > b :=
or_imp_or_left (le_or_gt a b) (assume H : a ≤ b, le_imp_lt_or_eq H)

theorem trichotomy (a b : ℤ) : a < b ∨ a = b ∨ a > b :=
iff_elim_left (or_assoc _ _ _) (trichotomy_alt a b)

theorem le_total (a b : ℤ) : a ≤ b ∨ b ≤ a :=
or_imp_or_right (le_or_gt a b) (assume H : b < a, lt_imp_le H)

theorem not_lt_imp_le {a b : ℤ} (H : ¬ a < b) : b ≤ a :=
resolve_left (le_or_gt b a) H

theorem not_le_imp_lt {a b : ℤ} (H : ¬ a ≤ b) : b < a :=
resolve_right (le_or_gt a b) H

-- (non)positivity and (non)negativity
-- -------------------------------------

-- ### basic

-- see also "int_by_cases" and similar theorems

theorem pos_imp_exists_nat {a : ℤ} (H : a ≥ 0) : ∃n : ℕ, a = n :=
obtain (n : ℕ) (Hn : of_nat 0 + n = a), from le_elim H,
exists_intro n (trans (symm Hn) (add_zero_left n))

theorem neg_imp_exists_nat {a : ℤ} (H : a ≤ 0) : ∃n : ℕ, a = -n :=
have H2 : -a ≥ 0, from zero_le_neg H,
obtain (n : ℕ) (Hn : -a = n), from pos_imp_exists_nat H2,
have H3 : a = -n, from symm (neg_move Hn),
exists_intro n H3

theorem to_nat_nonneg_eq {a : ℤ} (H : a ≥ 0) : (to_nat a) = a :=
obtain (n : ℕ) (Hn : a = n), from pos_imp_exists_nat H,
subst (symm Hn) (congr_arg of_nat (to_nat_of_nat n))

theorem of_nat_nonneg (n : ℕ) : of_nat n ≥ 0 :=
iff_mp (iff_symm (le_of_nat _ _)) (zero_le _)

theorem le_decidable [instance] {a b : ℤ} : decidable (a ≤ b) :=
have aux : ∀x, decidable (0 ≤ x), from
  take x,
    have H : 0 ≤ x ↔ of_nat (to_nat x) = x, from
      iff_intro
        (assume H1, to_nat_nonneg_eq H1)
        (assume H1, subst H1 (of_nat_nonneg (to_nat x))),
    decidable_iff_equiv _ (iff_symm H),
decidable_iff_equiv (aux _) (iff_symm (le_iff_sub_nonneg a b))

theorem ge_decidable [instance] {a b : ℤ} : decidable (a ≥ b)
theorem lt_decidable [instance] {a b : ℤ} : decidable (a < b)
theorem gt_decidable [instance] {a b : ℤ} : decidable (a > b)

--to_nat_neg is already taken... rename?
theorem to_nat_negative {a : ℤ} (H : a ≤ 0) : (to_nat a) = -a :=
obtain (n : ℕ) (Hn : a = -n), from neg_imp_exists_nat H,
calc
  (to_nat a) = (to_nat ( -n)) : {Hn}
  ... = (to_nat n) : {to_nat_neg n}
  ... = n : {to_nat_of_nat n}
  ... = -a : symm (neg_move (symm Hn))

theorem to_nat_cases (a : ℤ) : a = (to_nat a) ∨ a = - (to_nat a) :=
or_imp_or (le_total 0 a)
  (assume H : a ≥ 0, symm (to_nat_nonneg_eq H))
  (assume H : a ≤ 0, symm (neg_move (symm (to_nat_negative H))))

-- ### interaction of mul with le and lt

theorem mul_le_left_nonneg {a b c : ℤ} (Ha : a ≥ 0) (H : b ≤ c) : a * b ≤ a * c :=
obtain (n : ℕ) (Hn : b + n = c), from le_elim H,
have H2 : a * b + of_nat ((to_nat a) * n) = a * c, from
  calc
    a * b + of_nat ((to_nat a) * n) = a * b + (to_nat a) * of_nat n : by simp
      ... = a * b + a * n : {to_nat_nonneg_eq Ha}
      ... = a * (b + n) : by simp
      ... = a * c : by simp,
le_intro H2

theorem mul_le_right_nonneg {a b c : ℤ} (Hb : b ≥ 0) (H : a ≤ c) : a * b ≤ c * b :=
subst (mul_comm b c) (subst (mul_comm b a) (mul_le_left_nonneg Hb H))

theorem mul_le_left_nonpos {a b c : ℤ} (Ha : a ≤ 0) (H : b ≤ c) : a * c ≤ a * b :=
have H2 : -a * b ≤ -a * c, from mul_le_left_nonneg (zero_le_neg Ha) H,
have H3 : -(a * b) ≤ -(a * c), from subst (mul_neg_left a c) (subst (mul_neg_left a b) H2),
le_neg_inv H3

theorem mul_le_right_nonpos {a b c : ℤ} (Hb : b ≤ 0) (H : c ≤ a) : a * b ≤ c * b :=
subst (mul_comm b c) (subst (mul_comm b a) (mul_le_left_nonpos Hb H))

---this theorem can be made more general by replacing either Ha with 0 ≤ a or Hb with 0 ≤ d...
theorem mul_le_nonneg {a b c d : ℤ} (Ha : a ≥ 0) (Hb : b ≥ 0) (Hc : a ≤ c) (Hd : b ≤ d)
  : a * b ≤ c * d :=
le_trans (mul_le_right_nonneg Hb Hc) (mul_le_left_nonneg (le_trans Ha Hc) Hd)

theorem mul_le_nonpos {a b c d : ℤ} (Ha : a ≤ 0) (Hb : b ≤ 0) (Hc : c ≤ a) (Hd : d ≤ b)
  : a * b ≤ c * d :=
le_trans (mul_le_right_nonpos Hb Hc) (mul_le_left_nonpos (le_trans Hc Ha) Hd)

theorem mul_lt_left_pos {a b c : ℤ} (Ha : a > 0) (H : b < c) : a * b < a * c :=
have H2 : a * b < a * b + a, from subst (add_zero_right (a * b)) (add_lt_left Ha (a * b)),
have H3 : a * b + a ≤ a * c, from subst (by simp) (mul_le_left_nonneg (lt_imp_le Ha) H),
lt_le_trans H2 H3

theorem mul_lt_right_pos {a b c : ℤ} (Hb : b > 0) (H : a < c) : a * b < c * b :=
subst (mul_comm b c) (subst (mul_comm b a) (mul_lt_left_pos Hb H))

theorem mul_lt_left_neg {a b c : ℤ} (Ha : a < 0) (H : b < c) : a * c < a * b :=
have H2 : -a * b < -a * c, from mul_lt_left_pos (zero_lt_neg Ha) H,
have H3 : -(a * b) < -(a * c), from subst (mul_neg_left a c) (subst (mul_neg_left a b) H2),
lt_neg_inv H3

theorem mul_lt_right_neg {a b c : ℤ} (Hb : b < 0) (H : c < a) : a * b < c * b :=
subst (mul_comm b c) (subst (mul_comm b a) (mul_lt_left_neg Hb H))

theorem mul_le_lt_pos {a b c d : ℤ} (Ha : a > 0) (Hb : b ≥ 0) (Hc : a ≤ c) (Hd : b < d)
  : a * b < c * d :=
le_lt_trans (mul_le_right_nonneg Hb Hc) (mul_lt_left_pos (lt_le_trans Ha Hc) Hd)

theorem mul_lt_le_pos {a b c d : ℤ} (Ha : a ≥ 0) (Hb : b > 0) (Hc : a < c) (Hd : b ≤ d)
  : a * b < c * d :=
lt_le_trans (mul_lt_right_pos Hb Hc) (mul_le_left_nonneg (le_trans Ha (lt_imp_le Hc)) Hd)

theorem mul_lt_pos {a b c d : ℤ} (Ha : a > 0) (Hb : b > 0) (Hc : a < c) (Hd : b < d)
  : a * b < c * d :=
mul_lt_le_pos (lt_imp_le Ha) Hb Hc (lt_imp_le Hd)

theorem mul_lt_neg {a b c d : ℤ} (Ha : a < 0) (Hb : b < 0) (Hc : c < a) (Hd : d < b)
  : a * b < c * d :=
lt_trans (mul_lt_right_neg Hb Hc) (mul_lt_left_neg (lt_trans Hc Ha) Hd)

-- theorem mul_le_lt_neg and mul_lt_le_neg?

theorem mul_lt_cancel_left_nonneg {a b c : ℤ} (Hc : c ≥ 0) (H : c * a < c * b) : a < b :=
or_elim (le_or_gt b a)
  (assume H2 : b ≤ a,
    have H3 : c * b ≤ c * a, from mul_le_left_nonneg Hc H2,
    absurd_elim _ H3 (lt_imp_not_ge H))
  (assume H2 : a < b, H2)

theorem mul_lt_cancel_right_nonneg {a b c : ℤ} (Hc : c ≥ 0) (H : a * c < b * c) : a < b :=
mul_lt_cancel_left_nonneg Hc (subst (mul_comm b c) (subst (mul_comm a c) H))

theorem mul_lt_cancel_left_nonpos {a b c : ℤ} (Hc : c ≤ 0) (H : c * b < c * a) : a < b :=
have H2 : -(c * a) < -(c * b), from lt_neg H,
have H3 : -c * a < -c * b,
  from subst (symm (mul_neg_left c b)) (subst (symm (mul_neg_left c a)) H2),
have H4 : -c ≥ 0, from zero_le_neg Hc,
mul_lt_cancel_left_nonneg H4 H3

theorem mul_lt_cancel_right_nonpos {a b c : ℤ} (Hc : c ≤ 0) (H : b * c < a * c) : a < b :=
mul_lt_cancel_left_nonpos Hc (subst (mul_comm b c) (subst (mul_comm a c) H))

theorem mul_le_cancel_left_pos {a b c : ℤ} (Hc : c > 0) (H : c * a ≤ c * b) : a ≤ b :=
or_elim (le_or_gt a b)
  (assume H2 : a ≤ b, H2)
  (assume H2 : a > b,
    have H3 : c * a > c * b, from mul_lt_left_pos Hc H2,
    absurd_elim _ H3 (le_imp_not_gt H))

theorem mul_le_cancel_right_pos {a b c : ℤ} (Hc : c > 0) (H : a * c ≤ b * c) : a ≤ b :=
mul_le_cancel_left_pos Hc (subst (mul_comm b c) (subst (mul_comm a c) H))

theorem mul_le_cancel_left_neg {a b c : ℤ} (Hc : c < 0) (H : c * b ≤ c * a) : a ≤ b :=
have H2 : -(c * a) ≤ -(c * b), from le_neg H,
have H3 : -c * a ≤ -c * b,
  from subst (symm (mul_neg_left c b)) (subst (symm (mul_neg_left c a)) H2),
have H4 : -c > 0, from zero_lt_neg Hc,
mul_le_cancel_left_pos H4 H3

theorem mul_le_cancel_right_neg {a b c : ℤ} (Hc : c < 0) (H : b * c ≤ a * c) : a ≤ b :=
mul_le_cancel_left_neg Hc (subst (mul_comm b c) (subst (mul_comm a c) H))

theorem mul_eq_one_left {a b : ℤ} (H : a * b = 1) : a = 1 ∨ a = - 1 :=
have H2 : (to_nat a) * (to_nat b) = 1, from
  calc
    (to_nat a) * (to_nat b) = (to_nat (a * b)) : symm (mul_to_nat a b)
      ... = (to_nat 1) : {H}
      ... = 1 : to_nat_of_nat 1,
have H3 : (to_nat a) = 1, from mul_eq_one_left H2,
or_imp_or (to_nat_cases a)
  (assume H4 : a = (to_nat a), subst H3 H4)
  (assume H4 : a = - (to_nat a), subst H3 H4)

theorem mul_eq_one_right {a b : ℤ} (H : a * b = 1) : b = 1 ∨ b = - 1 :=
mul_eq_one_left (subst (mul_comm a b) H)


-- sign function
-- -------------

definition sign (a : ℤ) : ℤ := if a > 0 then 1 else (if a < 0 then - 1 else 0)

-- TODO: for kernel
theorem or_elim3 {a b c d : Prop} (H : a ∨ b ∨ c) (Ha : a → d) (Hb : b → d) (Hc : c → d) : d :=
or_elim H Ha (assume H2,or_elim H2 Hb Hc)

theorem sign_pos {a : ℤ} (H : a > 0) : sign a = 1 :=
if_pos H _ _

theorem sign_negative {a : ℤ} (H : a < 0) : sign a = - 1 :=
trans (if_neg (lt_antisym H) _ _) (if_pos H  _ _)

theorem sign_zero : sign 0 = 0 :=
trans (if_neg (lt_irrefl 0) _ _) (if_neg (lt_irrefl 0)  _ _)

-- add_rewrite sign_negative sign_pos to_nat_negative to_nat_nonneg_eq sign_zero mul_to_nat

theorem mul_sign_to_nat (a : ℤ) : sign a * (to_nat a) = a :=
have temp1 : ∀a : ℤ, a < 0 → a ≤ 0, from take a, lt_imp_le,
have temp2 : ∀a : ℤ, a > 0 → a ≥ 0, from take a, lt_imp_le,
or_elim3 (trichotomy a 0)
  (assume H : a < 0, by simp)
  (assume H : a = 0, by simp)
  (assume H : a > 0, by simp)

-- TODO: show decidable for equality (and avoid classical library)
theorem sign_mul (a b : ℤ) : sign (a * b) = sign a * sign b :=
or_elim (em (a = 0))
  (assume Ha : a = 0, by simp)
  (assume Ha : a ≠ 0,
    or_elim (em (b = 0))
      (assume Hb : b = 0, by simp)
      (assume Hb : b ≠ 0,
        have H : sign (a * b) * (to_nat (a * b)) = sign a * sign b  * (to_nat (a * b)), from
          calc
            sign (a * b) * (to_nat (a * b)) = a * b : mul_sign_to_nat (a * b)
              ... = sign a * (to_nat a) * b : {symm (mul_sign_to_nat a)}
              ... = sign a * (to_nat a) * (sign b * (to_nat b)) : {symm (mul_sign_to_nat b)}
              ... = sign a * sign b  * (to_nat (a * b)) : by simp,
        have H2 : (to_nat (a * b)) ≠ 0, from
          take H2', mul_ne_zero Ha Hb (to_nat_eq_zero H2'),
        have H3 : (to_nat (a * b)) ≠ of_nat 0, from contrapos of_nat_inj H2,
        mul_cancel_right H3 H))

--set_option pp::coercion true

theorem sign_idempotent (a : ℤ) : sign (sign a) = sign a :=
have temp : of_nat 1 > 0, from iff_elim_left (iff_symm (lt_of_nat 0 1)) (succ_pos 0),
    --this should be done with simp
or_elim3 (trichotomy a 0) sorry sorry sorry
--  (by simp)
--  (by simp)
--  (by simp)

theorem sign_succ (n : ℕ) : sign (succ n) = 1 :=
sign_pos (iff_elim_left (iff_symm (lt_of_nat 0 (succ n))) (succ_pos n))
  --this should be done with simp

theorem sign_neg (a : ℤ) : sign (-a) = - sign a :=
have temp1 : a > 0 → -a < 0, from neg_lt_zero,
have temp2 : a < 0 → -a > 0, from zero_lt_neg,
or_elim3 (trichotomy a 0) sorry sorry sorry
--  (by simp)
--  (by simp)
--  (by simp)

-- add_rewrite sign_neg

theorem to_nat_sign_ne_zero {a : ℤ} (H : a ≠ 0) : (to_nat (sign a)) = 1 :=
or_elim3 (trichotomy a 0) sorry
--  (by simp)
  (assume H2 : a = 0, absurd_elim _ H2 H)
  sorry
--  (by simp)

theorem sign_to_nat (a : ℤ) : sign (to_nat a) = to_nat (sign a) :=
have temp1 : ∀a : ℤ, a < 0 → a ≤ 0, from take a, lt_imp_le,
have temp2 : ∀a : ℤ, a > 0 → a ≥ 0, from take a, lt_imp_le,
or_elim3 (trichotomy a 0) sorry sorry sorry
--  (by simp)
--  (by simp)
--  (by simp)


-- set_opaque rel true
-- set_opaque rep true
-- set_opaque of_nat true
-- set_opaque to_nat true
-- set_opaque neg true
-- set_opaque add true
-- set_opaque mul true
-- set_opaque le true
-- set_opaque lt true
-- set_opaque sign true
--transparent: sub ge gt

end int -- namespace int
