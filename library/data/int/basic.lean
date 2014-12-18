/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: int.basic
Authors: Floris van Doorn, Jeremy Avigad

The integers, with addition, multiplication, and subtraction. The representation of the integers is
chosen to compute efficiently; see the examples in the comments at the end of this file.

To faciliate proving things about these operations, we show that the integers are a quotient of
ℕ × ℕ with the usual equivalence relation ≡, and functions

  abstr : ℕ × ℕ → ℤ
  repr : ℤ → ℕ × ℕ

satisfying

  abstr_repr (a : ℤ) : abstr (repr a) = a
  repr_abstr (p : ℕ × ℕ) : repr (abstr p) ≡ p
  abstr_eq (p q : ℕ × ℕ) : p ≡ q → abstr p = abstr q

For example, to "lift" statements about add to statements about padd, we need to prove the
following:

  repr_add (a b : ℤ) : repr (a + b) = padd (repr a) (repr b)
  padd_congr (p p' q q' : ℕ × ℕ) (H1 : p ≡ p') (H2 : q ≡ q') : padd p q ≡ p' q'
-/

import data.nat.basic data.nat.order data.nat.sub data.prod
import algebra.relation algebra.binary algebra.ordered_ring
import tools.fake_simplifier

open eq.ops
open prod relation nat
open decidable binary fake_simplifier

/- the type of integers -/

inductive int : Type :=
  of_nat : nat → int,
  neg_succ_of_nat : nat → int

notation `ℤ` := int
coercion [persistent] int.of_nat
definition int.of_num [coercion] (n : num) : ℤ := int.of_nat (nat.of_num n)

namespace int

/- computational definitions of basic functions -/

definition neg_of_nat (m : ℕ) : ℤ :=
nat.cases_on m 0 (take m', neg_succ_of_nat m')

definition sub_nat_nat (m n : ℕ) : ℤ :=
nat.cases_on (n - m)
  (of_nat (m - n))     -- m ≥ n
  (take k, neg_succ_of_nat k)   -- m < n, and n - m = succ k

definition neg (a : ℤ) : ℤ :=
  cases_on a
    (take m,                                           -- a = of_nat m
      nat.cases_on m 0 (take m', neg_succ_of_nat m'))
    (take m, of_nat (succ m))                          -- a = neg_succ_of_nat m

definition add (a b : ℤ) : ℤ :=
  cases_on a
    (take m,                                           -- a = of_nat m
      cases_on b
        (take n, of_nat (m + n))                         -- b = of_nat n
        (take n, sub_nat_nat m (succ n)))                -- b = neg_succ_of_nat n
    (take m,                                           -- a = neg_succ_of_nat m
      cases_on b
        (take n, sub_nat_nat n (succ m))                 -- b = of_nat n
        (take n, neg_of_nat (succ m + succ n)))          -- b = neg_succ_of_nat n

definition mul (a b : ℤ) : ℤ :=
  cases_on a
    (take m,                                           -- a = of_nat m
      cases_on b
        (take n, of_nat (m * n))                         -- b = of_nat n
        (take n, neg_of_nat (m * succ n)))               -- b = neg_succ_of_nat n
    (take m,                                           -- a = neg_succ_of_nat m
      cases_on b
        (take n, neg_of_nat (succ m * n))                -- b = of_nat n
        (take n, of_nat (succ m * succ n)))              -- b = neg_succ_of_nat n

/- notation -/

notation `-[` n `+1]` := int.neg_succ_of_nat n    -- for pretty-printing output
prefix - := int.neg
infix +  := int.add
infix *  := int.mul

/- some basic functions and properties -/

theorem of_nat_inj {m n : ℕ} (H : of_nat m = of_nat n) : m = n :=
no_confusion H (λe, e)

theorem neg_succ_of_nat_inj {m n : ℕ} (H : neg_succ_of_nat m = neg_succ_of_nat n) : m = n :=
no_confusion H (λe, e)

definition has_decidable_eq [instance] : decidable_eq ℤ :=
take a b,
cases_on a
  (take m,
    cases_on b
      (take n,
        if H : m = n then inl (congr_arg of_nat H) else inr (take H1, H (of_nat_inj H1)))
      (take n', inr (assume H, no_confusion H)))
  (take m',
    cases_on b
      (take n, inr (assume H, no_confusion H))
      (take n',
        (if H : m' = n' then inl (congr_arg neg_succ_of_nat H) else
            inr (take H1, H (neg_succ_of_nat_inj H1)))))

definition decidable_nonneg [instance] (a : ℤ) : decidable (nonneg a) := cases_on a _ _

definition decidable_le [instance] (a b : ℤ) : decidable (a ≤ b) := decidable_nonneg _

definition decidable_lt [instance] (a b : ℤ) : decidable (a < b) := decidable_nonneg _

theorem sub_nat_nat_of_ge {m n : ℕ} (H : m ≥ n) : sub_nat_nat m n = of_nat (m - n) :=
have H1 : n - m = 0, from le_imp_sub_eq_zero H,
calc
  sub_nat_nat m n = nat.cases_on 0 (of_nat (m - n)) _ : H1 ▸ rfl
    ... = of_nat (m - n) : rfl

theorem sub_nat_nat_of_lt {m n : ℕ} (H : m < n) :
  sub_nat_nat m n = neg_succ_of_nat (pred (n - m)) :=
have H1 : n - m = succ (pred (n - m)), from (succ_pred_of_pos (sub_pos_of_gt H))⁻¹,
calc
  sub_nat_nat m n = nat.cases_on (succ (pred (n - m))) (of_nat (m - n))
        (take k, neg_succ_of_nat k) : H1 ▸ rfl
    ... = neg_succ_of_nat (pred (n - m)) : rfl

definition nat_abs (a : ℤ) : ℕ := cases_on a (take n, n) (take n', succ n')

theorem nat_abs_of_nat (n : ℕ) : nat_abs (of_nat n) = n := rfl

theorem nat_abs_eq_zero {a : ℤ} : nat_abs a = 0 → a = 0 :=
cases_on a
  (take m, assume H : nat_abs (of_nat m) = 0, congr_arg of_nat H)
  (take m', assume H : nat_abs (neg_succ_of_nat m') = 0, absurd H (succ_ne_zero _))


/-
Show int is a quotient of ordered pairs of natural numbers, with the usual
equivalence relation.
-/

definition equiv (p q : ℕ × ℕ) : Prop :=  pr1 p + pr2 q = pr2 p + pr1 q

notation [local] p `≡` q := equiv p q

theorem equiv.refl {p : ℕ × ℕ} : p ≡ p := !add.comm

theorem equiv.symm {p q : ℕ × ℕ} (H : p ≡ q) : q ≡ p :=
calc
  pr1 q + pr2 p = pr2 p + pr1 q : !add.comm
    ... = pr1 p + pr2 q         : H⁻¹
    ... = pr2 q + pr1 p         : !add.comm

theorem equiv.trans {p q r : ℕ × ℕ} (H1 : p ≡ q) (H2 : q ≡ r) : p ≡ r :=
have H3 : pr1 p + pr2 r + pr2 q = pr2 p + pr1 r + pr2 q, from
  calc
   pr1 p + pr2 r + pr2 q = pr1 p + pr2 q + pr2 r : by simp
    ... = pr2 p + pr1 q + pr2 r                  : {H1}
    ... = pr2 p + (pr1 q + pr2 r)                : by simp
    ... = pr2 p + (pr2 q + pr1 r)                : {H2}
    ... = pr2 p + pr1 r + pr2 q                  : by simp,
show pr1 p + pr2 r = pr2 p + pr1 r, from add.cancel_right H3

theorem equiv_equiv : is_equivalence equiv :=
is_equivalence.mk @equiv.refl @equiv.symm @equiv.trans

theorem equiv_cases {p q : ℕ × ℕ} (H : equiv p q) :
    (pr1 p ≥ pr2 p ∧ pr1 q ≥ pr2 q) ∨ (pr1 p < pr2 p ∧ pr1 q < pr2 q) :=
or.elim (@le_or_gt (pr2 p) (pr1 p))
  (assume H1: pr1 p ≥ pr2 p,
    have H2 : pr2 p + pr1 q ≥ pr2 p + pr2 q, from H ▸ add_le_right H1 (pr2 q),
    or.inl (and.intro H1 (add_le_cancel_left H2)))
  (assume H1: pr1 p < pr2 p,
    have H2 : pr2 p + pr1 q < pr2 p + pr2 q, from H ▸ add_lt_right H1 (pr2 q),
    or.inr (and.intro H1 (add_lt_cancel_left H2)))

theorem equiv_of_eq {p q : ℕ × ℕ} (H : p = q) : p ≡ q := H ▸ equiv.refl

theorem equiv_of_eq_of_equiv {p q r : ℕ × ℕ} (H1 : p = q) (H2 : q ≡ r) : p ≡ r := H1⁻¹ ▸ H2

theorem equiv_of_equiv_of_eq {p q r : ℕ × ℕ} (H1 : p ≡ q) (H2 : q = r) : p ≡ r := H2 ▸ H1

calc_trans equiv.trans
calc_refl equiv.refl
calc_symm equiv.symm
calc_trans equiv_of_eq_of_equiv
calc_trans equiv_of_equiv_of_eq

/- the representation and abstraction functions -/

definition abstr (a : ℕ × ℕ) : ℤ := sub_nat_nat (pr1 a) (pr2 a)

theorem abstr_of_ge {p : ℕ × ℕ} (H : pr1 p ≥ pr2 p) : abstr p = of_nat (pr1 p - pr2 p) :=
sub_nat_nat_of_ge H

theorem abstr_of_lt {p : ℕ × ℕ} (H : pr1 p < pr2 p) :
  abstr p = neg_succ_of_nat (pred (pr2 p - pr1 p)) :=
sub_nat_nat_of_lt H

definition repr (a : ℤ) : ℕ × ℕ := cases_on a (take m, (m, 0)) (take m, (0, succ m))

theorem abstr_repr (a : ℤ) : abstr (repr a) = a :=
cases_on a (take m, (sub_nat_nat_of_ge (zero_le m))) (take m, rfl)

theorem repr_sub_nat_nat (m n : ℕ) : repr (sub_nat_nat m n) ≡ (m, n) :=
or.elim (@le_or_gt n m)
  (take H : m ≥ n,
    have H1 : repr (sub_nat_nat m n) = (m - n, 0), from sub_nat_nat_of_ge H ▸ rfl,
    H1⁻¹ ▸
      (calc
        m - n + n = m : add_sub_ge_left H
          ... = 0 + m : add.zero_left))
  (take H : m < n,
    have H1 : repr (sub_nat_nat m n) = (0, succ (pred (n - m))), from sub_nat_nat_of_lt H ▸ rfl,
    H1⁻¹ ▸
      (calc
        0 + n = n : add.zero_left
          ... = n - m + m : add_sub_ge_left (lt_imp_le H)
          ... = succ (pred (n - m)) + m : (succ_pred_of_pos (sub_pos_of_gt H))⁻¹))

theorem repr_abstr (p : ℕ × ℕ) : repr (abstr p) ≡ p :=
!prod.eta ▸ !repr_sub_nat_nat

theorem abstr_eq {p q : ℕ × ℕ} (Hequiv : p ≡ q) : abstr p = abstr q :=
or.elim (equiv_cases Hequiv)
  (assume H2,
    have H3 : pr1 p ≥ pr2 p, from and.elim_left H2,
    have H4 : pr1 q ≥ pr2 q, from and.elim_right H2,
    have H5 : pr1 p = pr1 q - pr2 q + pr2 p, from
      calc
        pr1 p = pr1 p + pr2 q - pr2 q : sub_add_left
          ... = pr2 p + pr1 q - pr2 q : Hequiv
          ... = pr2 p + (pr1 q - pr2 q) : add_sub_assoc H4
          ... = pr1 q - pr2 q + pr2 p : add.comm,
    have H6 : pr1 p - pr2 p = pr1 q - pr2 q, from
      calc
        pr1 p - pr2 p = pr1 q - pr2 q + pr2 p - pr2 p : H5
          ... = pr1 q - pr2 q : sub_add_left,
    abstr_of_ge H3 ⬝ congr_arg of_nat H6 ⬝ (abstr_of_ge H4)⁻¹)
  (assume H2,
    have H3 : pr1 p < pr2 p, from and.elim_left H2,
    have H4 : pr1 q < pr2 q, from and.elim_right H2,
    have H5 : pr2 p = pr2 q - pr1 q + pr1 p, from
      calc
        pr2 p = pr2 p + pr1 q - pr1 q : sub_add_left
          ... = pr1 p + pr2 q - pr1 q : Hequiv
          ... = pr1 p + (pr2 q - pr1 q) : add_sub_assoc (lt_imp_le H4)
          ... = pr2 q - pr1 q + pr1 p : add.comm,
    have H6 : pr2 p - pr1 p = pr2 q - pr1 q, from
      calc
        pr2 p - pr1 p = pr2 q - pr1 q + pr1 p - pr1 p : H5
          ... = pr2 q - pr1 q : sub_add_left,
    abstr_of_lt H3 ⬝ congr_arg neg_succ_of_nat (congr_arg pred H6)⬝ (abstr_of_lt H4)⁻¹)

theorem equiv_iff (p q : ℕ × ℕ) : (p ≡ q) ↔ ((p ≡ p) ∧ (q ≡ q) ∧ (abstr p = abstr q)) :=
iff.intro
  (assume H : equiv p q,
    and.intro !equiv.refl (and.intro !equiv.refl (abstr_eq H)))
  (assume H : equiv p p ∧ equiv q q ∧ abstr p = abstr q,
    have H1 : abstr p = abstr q, from and.elim_right (and.elim_right H),
    equiv.trans (H1 ▸ equiv.symm (repr_abstr p)) (repr_abstr q))

theorem eq_abstr_of_equiv_repr {a : ℤ} {p : ℕ × ℕ} (Hequiv : repr a ≡ p) : a = abstr p :=
calc
  a = abstr (repr a) : abstr_repr
   ... = abstr p : abstr_eq Hequiv

theorem eq_of_repr_equiv_repr {a b : ℤ} (H : repr a ≡ repr b) : a = b :=
calc
  a = abstr (repr a) : abstr_repr
    ... = abstr (repr b) : abstr_eq H
    ... = b : abstr_repr

theorem nat_abs_abstr (p : ℕ × ℕ) : nat_abs (abstr p) = dist (pr1 p) (pr2 p) :=
let m := pr1 p, n := pr2 p in
or.elim (@le_or_gt n m)
  (assume H : m ≥ n,
    calc
      nat_abs (abstr (m, n)) = nat_abs (of_nat (m - n)) : int.abstr_of_ge H
        ... = dist m n : dist_ge H)
  (assume H : m < n,
    calc
      nat_abs (abstr (m, n)) = nat_abs (neg_succ_of_nat (pred (n - m))) : int.abstr_of_lt H
        ... = succ (pred (n - m)) : rfl
        ... = n - m : succ_pred_of_pos (sub_pos_of_gt H)
        ... = dist m n : dist_le (lt_imp_le H))

theorem cases (a : ℤ) : (∃n : ℕ, a = of_nat n) ∨ (∃n : ℕ, a = - of_nat n) :=
cases_on a
  (take n, or.inl (exists.intro n rfl))
  (take n', or.inr (exists.intro (succ n') rfl))

theorem by_cases {P : ℤ → Prop} (a : ℤ) (H1 : ∀n : ℕ, P (of_nat n)) (H2 : ∀n : ℕ, P (- of_nat n)) :
  P a :=
or.elim (cases a)
  (assume H, obtain (n : ℕ) (H3 : a = n), from H, H3⁻¹ ▸ H1 n)
  (assume H, obtain (n : ℕ) (H3 : a = -n), from H, H3⁻¹ ▸ H2 n)

/-
Show int is a ring.
-/

/- addition -/

definition padd (p q : ℕ × ℕ) : ℕ × ℕ := map_pair2 nat.add p q

theorem repr_add (a b : ℤ) :  repr (add a b) ≡ padd (repr a) (repr b) :=
cases_on a
  (take m,
    cases_on b
      (take n, !equiv.refl)
      (take n',
        have H1 : equiv (repr (add (of_nat m) (neg_succ_of_nat n'))) (m, succ n'),
          from !repr_sub_nat_nat,
        have H2 : padd (repr (of_nat m)) (repr (neg_succ_of_nat n')) = (m, 0 + succ n'),
          from rfl,
        (!add.zero_left ▸ H2)⁻¹ ▸ H1))
  (take m',
    cases_on b
      (take n,
        have H1 : equiv (repr (add (neg_succ_of_nat m') (of_nat n))) (n, succ m'),
          from !repr_sub_nat_nat,
        have H2 : padd (repr (neg_succ_of_nat m')) (repr (of_nat n)) = (0 + n, succ m'),
          from rfl,
        (!add.zero_left ▸ H2)⁻¹ ▸ H1)
       (take n',!repr_sub_nat_nat))

theorem padd_congr {p p' q q' : ℕ × ℕ} (Ha : p ≡ p') (Hb : q ≡ q') : padd p q ≡ padd p' q' :=
calc
  pr1 (padd p q) + pr2 (padd p' q') = pr1 p + pr2 p' + (pr1 q + pr2 q') : by simp
    ... = pr2 p + pr1 p' + (pr1 q + pr2 q') : {Ha}
    ... = pr2 p + pr1 p' + (pr2 q + pr1 q') : {Hb}
    ... = pr2 (padd p q) + pr1 (padd p' q') : by simp

theorem padd_comm (p q : ℕ × ℕ) : padd p q = padd q p :=
calc
  padd p q = (pr1 p + pr1 q, pr2 p + pr2 q) : rfl
    ... = (pr1 q + pr1 p, pr2 p + pr2 q) : add.comm
    ... = (pr1 q + pr1 p, pr2 q + pr2 p) : add.comm
    ... = padd q p : rfl

theorem padd_assoc (p q r : ℕ × ℕ) : padd (padd p q) r = padd p (padd q r) :=
calc
  padd (padd p q) r = (pr1 p + pr1 q + pr1 r, pr2 p + pr2 q + pr2 r) : rfl
    ... = (pr1 p + (pr1 q + pr1 r), pr2 p + pr2 q + pr2 r) : add.assoc
    ... = (pr1 p + (pr1 q + pr1 r), pr2 p + (pr2 q + pr2 r)) : add.assoc
    ... = padd p (padd q r) : rfl

theorem add.comm (a b : ℤ) : a + b = b + a :=
begin
  apply eq_of_repr_equiv_repr,
  apply equiv.trans,
  apply repr_add,
  apply equiv.symm,
  apply (eq.subst (padd_comm (repr b) (repr a))),
  apply repr_add
end

theorem add.assoc (a b c : ℤ) : a + b + c = a + (b + c) :=
have H1 [visible]: repr (a + b + c) ≡ padd (padd (repr a) (repr b)) (repr c), from
  equiv.trans (repr_add (a + b) c) (padd_congr !repr_add !equiv.refl),
have H2 [visible]: repr (a + (b + c)) ≡ padd (repr a) (padd (repr b) (repr c)), from
  equiv.trans (repr_add a (b + c)) (padd_congr !equiv.refl !repr_add),
begin
  apply eq_of_repr_equiv_repr,
  apply equiv.trans,
  apply H1,
  apply (eq.subst ((padd_assoc _ _ _)⁻¹)),
  apply equiv.symm,
  apply H2
end

theorem add.right_id (a : ℤ) : a + 0 = a := cases_on a (take m, rfl) (take m', rfl)

theorem add.left_id (a : ℤ) : 0 + a = a := add.comm a 0 ▸ add.right_id a

/- negation -/

definition pneg (p : ℕ × ℕ) : ℕ × ℕ := (pr2 p, pr1 p)

-- note: this is =, not just ≡
theorem repr_neg (a : ℤ) : repr (- a) = pneg (repr a) :=
cases_on a
  (take m,
    nat.cases_on m rfl (take m', rfl))
  (take m', rfl)

theorem pneg_congr {p p' : ℕ × ℕ} (H : p ≡ p') : pneg p ≡ pneg p' := eq.symm H

theorem pneg_pneg (p : ℕ × ℕ) : pneg (pneg p) = p := !prod.eta

theorem nat_abs_neg (a : ℤ) : nat_abs (-a) = nat_abs a :=
calc
  nat_abs (-a) = nat_abs (abstr (repr (-a))) : abstr_repr
    ... = nat_abs (abstr (pneg (repr a))) : repr_neg
    ... = dist (pr1 (pneg (repr a))) (pr2 (pneg (repr a))) : nat_abs_abstr
    ... = dist (pr2 (pneg (repr a))) (pr1 (pneg (repr a))) : dist_comm
    ... = nat_abs (abstr (repr a)) : nat_abs_abstr
    ... = nat_abs a : abstr_repr

theorem padd_pneg (p : ℕ × ℕ) : padd p (pneg p) ≡ (0, 0) :=
show pr1 p + pr2 p + 0 = pr2 p + pr1 p + 0, from !nat.add.comm ▸ rfl

theorem padd_padd_pneg (p q : ℕ × ℕ) : padd (padd p q) (pneg q) ≡ p :=
show pr1 p + pr1 q + pr2 q + pr2 p = pr2 p + pr2 q + pr1 q + pr1 p, by simp

theorem add.left_inv (a : ℤ) : -a + a = 0 :=
have H : repr (-a + a) ≡ repr 0, from
  calc
    repr (-a + a) ≡ padd (repr (neg a)) (repr a) : repr_add
      ... = padd (pneg (repr a)) (repr a) : repr_neg
      ... ≡ repr 0 : padd_pneg,
eq_of_repr_equiv_repr H

/- multiplication -/

definition pmul (p q : ℕ × ℕ) : ℕ × ℕ :=
  (pr1 p * pr1 q + pr2 p * pr2 q, pr1 p * pr2 q + pr2 p * pr1 q)

theorem repr_neg_of_nat (m : ℕ) : repr (neg_of_nat m) = (0, m) :=
nat.cases_on m rfl (take m', rfl)

-- note: we have =, not just ≡
theorem repr_mul (a b : ℤ) :  repr (mul a b) = pmul (repr a) (repr b) :=
cases_on a
  (take m,
    cases_on b
      (take n,
        (calc
          pmul (repr m) (repr n) = (m * n + 0 * 0, m * 0 + 0 * n) : rfl
            ... = (m * n + 0 * 0, m * 0 + 0) : mul.zero_left)⁻¹)
      (take n',
        (calc
          pmul (repr m) (repr (neg_succ_of_nat n')) =
              (m * 0 + 0 * succ n', m * succ n' + 0 * 0) : rfl
            ... = (m * 0 + 0, m * succ n' + 0 * 0) : mul.zero_left
            ... = repr (mul m (neg_succ_of_nat n')) : repr_neg_of_nat)⁻¹))
  (take m',
    cases_on b
      (take n,
        (calc
          pmul (repr (neg_succ_of_nat m')) (repr n) =
              (0 * n + succ m' * 0, 0 * 0 + succ m' * n) : rfl
            ... = (0 + succ m' * 0, 0 * 0 + succ m' * n) : mul.zero_left
            ... = (0 + succ m' * 0, succ m' * n) : add.zero_left
            ... = repr (mul (neg_succ_of_nat m') n) : repr_neg_of_nat)⁻¹)
      (take n',
        (calc
          pmul (repr (neg_succ_of_nat m')) (repr (neg_succ_of_nat n')) =
              (0 + succ m' * succ n', 0 * succ n') : rfl
            ... = (succ m' * succ n', 0 * succ n') : add.zero_left
            ... = (succ m' * succ n', 0) : mul.zero_left
            ... = repr (mul (neg_succ_of_nat m') (neg_succ_of_nat n')) : rfl)⁻¹))

theorem equiv_mul_prep {xa ya xb yb xn yn xm ym : ℕ}
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

theorem pmul_congr {p p' q q' : ℕ × ℕ} (H1 : p ≡ p') (H2 : q ≡ q') : pmul p q ≡ pmul p' q' :=
equiv_mul_prep H1 H2

theorem pmul_comm (p q : ℕ × ℕ) : pmul p q = pmul q p :=
calc
  (pr1 p * pr1 q + pr2 p * pr2 q, pr1 p * pr2 q + pr2 p * pr1 q) =
      (pr1 q * pr1 p + pr2 p * pr2 q, pr1 p * pr2 q + pr2 p * pr1 q) : mul.comm
    ... = (pr1 q * pr1 p + pr2 q * pr2 p, pr1 p * pr2 q + pr2 p * pr1 q) : mul.comm
    ... = (pr1 q * pr1 p + pr2 q * pr2 p, pr2 q * pr1 p + pr2 p * pr1 q) : mul.comm
    ... = (pr1 q * pr1 p + pr2 q * pr2 p, pr2 q * pr1 p + pr1 q * pr2 p) : mul.comm
    ... = (pr1 q * pr1 p + pr2 q * pr2 p, pr1 q * pr2 p + pr2 q * pr1 p) : nat.add.comm

theorem mul.comm (a b : ℤ) : a * b = b * a :=
eq_of_repr_equiv_repr
  ((calc
    repr (a * b) = pmul (repr a) (repr b) : repr_mul
      ... = pmul (repr b) (repr a) : pmul_comm
      ... = repr (b * a) : repr_mul) ▸ !equiv.refl)

theorem pmul_assoc (p q r: ℕ × ℕ) : pmul (pmul p q) r = pmul p (pmul q r) :=
by simp

theorem mul.assoc (a b c : ℤ) : (a * b) * c = a * (b * c) :=
eq_of_repr_equiv_repr
  ((calc
    repr (a * b * c) = pmul (repr (a * b)) (repr c) : repr_mul
      ... = pmul (pmul (repr a) (repr b)) (repr c) : repr_mul
      ... = pmul (repr a) (pmul (repr b) (repr c)) : pmul_assoc
      ... = pmul (repr a) (repr (b * c)) : repr_mul
      ... = repr (a * (b * c)) : repr_mul) ▸ !equiv.refl)

theorem mul.right_id (a : ℤ) : a * 1 = a :=
eq_of_repr_equiv_repr (equiv_of_eq
  ((calc
    repr (a * 1) = pmul (repr a) (repr 1) : repr_mul
      ... = (pr1 (repr a), pr2 (repr a)) : by simp
      ... = repr a : prod.eta)))

theorem mul.left_id (a : ℤ) : 1 * a = a :=
mul.comm a 1 ▸ mul.right_id a

theorem mul.right_distrib (a b c : ℤ) : (a + b) * c = a * c + b * c :=
eq_of_repr_equiv_repr
  (calc
    repr ((a + b) * c) = pmul (repr (a + b)) (repr c) : repr_mul
      ... ≡ pmul (padd (repr a) (repr b)) (repr c) : pmul_congr !repr_add equiv.refl
      ... = padd (pmul (repr a) (repr c)) (pmul (repr b) (repr c)) : by simp
      ... = padd (repr (a * c)) (pmul (repr b) (repr c)) : {(repr_mul a c)⁻¹}
      ... = padd (repr (a * c)) (repr (b * c)) : repr_mul
      ... ≡ repr (a * c + b * c) : equiv.symm !repr_add)

theorem mul.left_distrib (a b c : ℤ) : a * (b + c) = a * b + a * c :=
calc
  a * (b + c) = (b + c) * a : mul.comm a (b + c)
    ... = b * a + c * a : mul.right_distrib b c a
    ... = a * b + c * a : {mul.comm b a}
    ... = a * b + a * c : {mul.comm c a}

theorem zero_ne_one : (typeof 0 : int) ≠ 1 :=
assume H : 0 = 1,
show false, from succ_ne_zero 0 ((of_nat_inj H)⁻¹)

definition comm_ring : algebra.comm_ring int :=
algebra.comm_ring.mk add add.assoc zero add.left_id add.right_id neg add.left_inv
add.comm mul mul.assoc (of_num 1) mul.left_id mul.right_id mul.left_distrib mul.right_distrib
zero_ne_one mul.comm

/-
Instantiate ring theorems to int
-/

context port_algebra
  open algebra    -- TODO: can we "open" algebra only for the duration of this section?
  instance comm_ring

  theorem mul.left_comm : ∀a b c : ℤ, a * (b * c) = b * (a * c) := algebra.mul.left_comm
  theorem mul.right_comm : ∀a b c : ℤ, (a * b) * c = (a * c) * b := algebra.mul.right_comm
  theorem add.left_comm : ∀a b c : ℤ, a + (b + c) = b + (a + c) := algebra.add.left_comm
  theorem add.right_comm : ∀a b c : ℤ, (a + b) + c = (a + c) + b := algebra.add.right_comm
  theorem add.left_cancel : ∀{a b c : ℤ}, a + b = a + c → b = c := @algebra.add.left_cancel _ _
  theorem add.right_cancel : ∀{a b c : ℤ}, a + b = c + b → a = c := @algebra.add.right_cancel _ _
  theorem neg_add_cancel_left : ∀a b : ℤ, -a + (a + b) = b := algebra.neg_add_cancel_left
  theorem neg_add_cancel_right : ∀a b : ℤ, a + -b + b = a := algebra.neg_add_cancel_right
  theorem neg_eq_of_add_eq_zero : ∀{a b : ℤ}, a + b = 0 → -a = b :=
    @algebra.neg_eq_of_add_eq_zero _ _
  theorem neg_zero : -0 = 0 := algebra.neg_zero
  theorem neg_neg : ∀a : ℤ, -(-a) = a := algebra.neg_neg
  theorem neg.inj : ∀{a b : ℤ}, -a = -b → a = b := @algebra.neg.inj _ _
  theorem neg_eq_neg_iff_eq : ∀a b : ℤ, -a = -b ↔ a = b := algebra.neg_eq_neg_iff_eq
  theorem neg_eq_zero_iff_eq_zero : ∀a : ℤ, -a = 0 ↔ a = 0 := algebra.neg_eq_zero_iff_eq_zero
  theorem eq_neg_of_eq_neg : ∀{a b : ℤ}, a = -b → b = -a := @algebra.eq_neg_of_eq_neg _ _
  theorem eq_neg_iff_eq_neg : ∀{a b : ℤ}, a = -b ↔ b = -a := @algebra.eq_neg_iff_eq_neg _ _
  theorem add.right_inv : ∀a : ℤ, a + -a = 0 := algebra.add.right_inv
  theorem add_neg_cancel_left : ∀a b : ℤ, a + (-a + b) = b := algebra.add_neg_cancel_left
  theorem add_neg_cancel_right : ∀a b : ℤ, a + b + -b = a := algebra.add_neg_cancel_right
  theorem neg_add_eq : ∀a b : ℤ, -(a + b) = -b + -a := algebra.neg_add_eq
  theorem eq_add_neg_of_add_eq : ∀{a b c : ℤ}, a + b = c → a = c + -b :=
    @algebra.eq_add_neg_of_add_eq _ _
  theorem eq_neg_add_of_add_eq : ∀{a b c : ℤ}, a + b = c → b = -a + c :=
    @algebra.eq_neg_add_of_add_eq _ _
  theorem neg_add_eq_of_eq_add : ∀{a b c : ℤ}, a = b + c → -b + a = c :=
    @algebra.neg_add_eq_of_eq_add _ _
  theorem add_neg_eq_of_eq_add : ∀{a b c : ℤ}, a = b + c → a + -c = b :=
    @algebra.add_neg_eq_of_eq_add _ _
  theorem eq_add_of_add_neg_eq : ∀{a b c : ℤ}, a + -b = c → a = c + b :=
    @algebra.eq_add_of_add_neg_eq _ _
  theorem eq_add_of_neg_add_eq : ∀{a b c : ℤ}, -a + b = c → b = a + c :=
    @algebra.eq_add_of_neg_add_eq _ _
  theorem add_eq_of_eq_neg_add : ∀{a b c : ℤ}, a = -b + c → b + a = c :=
    @algebra.add_eq_of_eq_neg_add _ _
  theorem add_eq_of_eq_add_neg : ∀{a b c : ℤ}, a = b + -c → a + c = b :=
    @algebra.add_eq_of_eq_add_neg _ _
  theorem add_eq_iff_eq_neg_add : ∀a b c : ℤ, a + b = c ↔ b = -a + c :=
    @algebra.add_eq_iff_eq_neg_add _ _
  theorem add_eq_iff_eq_add_neg : ∀a b c : ℤ, a + b = c ↔ a = c + -b :=
    @algebra.add_eq_iff_eq_add_neg _ _

  definition sub (a b : ℤ) : ℤ := algebra.sub a b
  infix - := int.sub

  theorem sub_self : ∀a : ℤ, a - a = 0 := algebra.sub_self
  theorem sub_add_cancel : ∀a b : ℤ, a - b + b = a := algebra.sub_add_cancel
  theorem add_sub_cancel : ∀a b : ℤ, a + b - b = a := algebra.add_sub_cancel
  theorem eq_of_sub_eq_zero : ∀{a b : ℤ}, a - b = 0 → a = b := @algebra.eq_of_sub_eq_zero _ _
  theorem eq_iff_sub_eq_zero : ∀a b : ℤ, a = b ↔ a - b = 0 := algebra.eq_iff_sub_eq_zero
  theorem zero_sub_eq : ∀a : ℤ, 0 - a = -a := algebra.zero_sub_eq
  theorem sub_zero_eq : ∀a : ℤ, a - 0 = a := algebra.sub_zero_eq
  theorem sub_neg_eq_add : ∀a b : ℤ, a - (-b) = a + b := algebra.sub_neg_eq_add
  theorem neg_sub_eq : ∀a b : ℤ, -(a - b) = b - a := algebra.neg_sub_eq
  theorem add_sub_eq : ∀a b c : ℤ, a + (b - c) = a + b - c := algebra.add_sub_eq
  theorem sub_add_eq_sub_sub_swap : ∀a b c : ℤ, a - (b + c) = a - c - b :=
    algebra.sub_add_eq_sub_sub_swap
  theorem sub_eq_iff_eq_add : ∀a b c : ℤ, a - b = c ↔ a = c + b := algebra.sub_eq_iff_eq_add
  theorem eq_sub_iff_add_eq : ∀a b c : ℤ, a = b - c ↔ a + c = b := algebra.eq_sub_iff_add_eq
  theorem eq_iff_eq_of_sub_eq_sub : ∀{a b c d : ℤ}, a - b = c - d → a = b ↔ c = d :=
    @algebra.eq_iff_eq_of_sub_eq_sub _ _
  theorem sub_add_eq_sub_sub : ∀a b c : ℤ, a - (b + c) = a - b - c := algebra.sub_add_eq_sub_sub
  theorem neg_add_eq_sub : ∀a b : ℤ, -a + b = b - a := algebra.neg_add_eq_sub
  theorem neg_add_distrib : ∀a b : ℤ, -(a + b) = -a + -b := algebra.neg_add_distrib
  theorem sub_add_eq_add_sub : ∀a b c : ℤ, a - b + c = a + c - b := algebra.sub_add_eq_add_sub
  theorem sub_sub_eq : ∀a b c : ℤ, a - b - c = a - (b + c) := algebra.sub_sub_eq
  theorem add_sub_add_left_eq_sub : ∀a b c : ℤ, (c + a) - (c + b) = a - b :=
    algebra.add_sub_add_left_eq_sub
  theorem zero_mul_eq : ∀a : ℤ, 0 * a = 0 := algebra.zero_mul_eq
  theorem mul_zero_eq : ∀a : ℤ, a * 0 = 0 := algebra.mul_zero_eq
  theorem neg_mul_eq_neg_mul : ∀a b : ℤ, -(a * b) = -a * b := algebra.neg_mul_eq_neg_mul
  theorem neg_mul_eq_mul_neg : ∀a b : ℤ, -(a * b) = a * -b := algebra.neg_mul_eq_mul_neg
  theorem neg_mul_neg_eq : ∀a b : ℤ, -a * -b = a * b := algebra.neg_mul_neg_eq
  theorem neg_mul_comm : ∀a b : ℤ, -a * b = a * -b := algebra.neg_mul_comm
  theorem mul_sub_left_distrib : ∀a b c : ℤ, a * (b - c) = a * b - a * c :=
    algebra.mul_sub_left_distrib
  theorem mul_sub_right_distrib : ∀a b c : ℤ, (a - b) * c = a * c - b * c :=
    algebra.mul_sub_right_distrib
  theorem mul_add_eq_mul_add_iff_sub_mul_add_eq :
      ∀a b c d e : ℤ, a * e + c = b * e + d ↔ (a - b) * e + c = d :=
    algebra.mul_add_eq_mul_add_iff_sub_mul_add_eq
  theorem mul_self_sub_mul_self_eq : ∀a b : ℤ, a * a - b * b = (a + b) * (a - b) :=
    algebra.mul_self_sub_mul_self_eq
  theorem mul_self_sub_one_eq : ∀a : ℤ, a * a - 1 = (a + 1) * (a - 1) :=
    algebra.mul_self_sub_one_eq

end port_algebra

definition nonneg (a : ℤ) : Prop := cases_on a (take n, true) (take n, false)
definition le (a b : ℤ) : Prop := nonneg (sub b a)
definition lt (a b : ℤ) : Prop := le (add a 1) b

infix - := int.sub
infix <= := int.le
infix ≤  := int.le
infix <  := int.lt

/-
  Other stuff.
  TODO: pare down and clean up.
-/

definition pabs (p : ℕ × ℕ) : ℕ := dist (pr1 p) (pr2 p)

theorem pabs_congr {p q : ℕ × ℕ} (H : p ≡ q) : pabs p = pabs q :=
calc
  pabs p = nat_abs (abstr p) : nat_abs_abstr
    ... = nat_abs (abstr q) : abstr_eq H
    ... = pabs q : nat_abs_abstr

theorem nat_abs_eq_pabs_repr (a : ℤ) : nat_abs a = pabs (repr a) :=
calc
  nat_abs a = nat_abs (abstr (repr a)) : abstr_repr
    ... = pabs (repr a) : nat_abs_abstr

theorem nat_abs_add_le (a b : ℤ) : nat_abs (a + b) ≤ nat_abs a + nat_abs b :=
have H : nat_abs (a + b) = pabs (padd (repr a) (repr b)), from
  calc
    nat_abs (a + b) = pabs (repr (a + b)) : nat_abs_eq_pabs_repr
      ... = pabs (padd (repr a) (repr b)) : pabs_congr !repr_add,
have H1 : nat_abs a = pabs (repr a), from !nat_abs_eq_pabs_repr,
have H2 : nat_abs b = pabs (repr b), from !nat_abs_eq_pabs_repr,
have H3 : pabs (padd (repr a) (repr b)) ≤ pabs (repr a) + pabs (repr b), from !dist_add_le_add_dist,
H⁻¹ ▸ H1⁻¹ ▸ H2⁻¹ ▸ H3

theorem add_of_nat (n m : nat) : of_nat n + of_nat m = #nat n + m := rfl

theorem of_nat_succ (n : ℕ) : of_nat (succ n) = of_nat n + 1 := rfl

theorem mul_of_nat (n m : ℕ) : of_nat n * of_nat m = n * m := rfl

theorem mul_nat_abs (a b : ℤ) : (nat_abs (a * b)) = #nat (nat_abs a) * (nat_abs b) :=
cases_on a
  (take m,
    cases_on b
      (take n, rfl)
      (take n', !nat_abs_neg ▸ rfl))
  (take m',
    cases_on b
      (take n, !nat_abs_neg ▸ rfl)
      (take n', rfl))

---reverse equalities, rename
theorem cases_succ (a : ℤ) : (∃n : ℕ, a = of_nat n) ∨ (∃n : ℕ, a = - (of_nat (succ n))) :=
or.elim (cases a)
  (assume H : (∃n : ℕ, a = of_nat n), or.inl H)
  (assume H,
    obtain (n : ℕ) (H2 : a = -(of_nat n)), from H,
    discriminate
      (assume H3 : n = nat.zero,
        have H4 : a = of_nat nat.zero, from
          calc
            a = -(of_nat n) : H2
          ... = -(of_nat nat.zero) : {H3}
          ... = of_nat nat.zero : neg_zero,
        or.inl (exists.intro nat.zero H4))
      (take k : ℕ,
        assume H3 : n = succ k,
        have H4 : a = -(of_nat (succ k)), from H3 ▸ H2,
        or.inr (exists.intro k H4)))

theorem int_by_cases_succ {P : ℤ → Prop} (a : ℤ)
  (H1 : ∀n : ℕ, P (of_nat n)) (H2 : ∀n : ℕ, P (-(of_nat (succ n)))) : P a :=
or.elim (cases_succ a)
  (assume H, obtain (n : ℕ) (H3 : a = of_nat n), from H, H3⁻¹ ▸ H1 n)
  (assume H, obtain (n : ℕ) (H3 : a = -(of_nat (succ n))), from H, H3⁻¹ ▸ H2 n)

theorem neg_sub'  (a b : ℤ) : -(a - b) = -a + b :=
calc
  -(a - b) = -a + -(-b) : neg_add_distrib a (-b)
    ... = -a + b : {neg_neg b}

theorem sub_add_assoc (a b c : ℤ) : a - b + c = a - (b - c) :=
calc
  a - b + c = a + (-b + c) : add.assoc a (-b) c
    ... = a + -(b - c) : {(neg_sub' b c)⁻¹}

theorem add_sub_assoc (a b c : ℤ) : a + b - c = a + (b - c) :=
add.assoc a b (-c)

theorem add_sub_inverse2 (a b : ℤ) : a + b - a = b :=
add.comm b a ▸ !add_sub_cancel

-- add_rewrite add_left_id add_right_id
-- add_rewrite add_comm add.assoc add_left_comm
-- add_rewrite sub_def add_inverse_right add_inverse_left
-- add_rewrite neg_add_distr
---- add_rewrite sub_sub_assoc sub_add_assoc add_sub_assoc
---- add_rewrite add_neg_right add_neg_left
---- add_rewrite sub_self

theorem mul_eq_zero {a b : ℤ} (H : a * b = 0) : a = 0 ∨ b = 0 :=
have H2 : (nat_abs a) * (nat_abs b) = nat.zero, from
  calc
    (nat_abs a) * (nat_abs b) = (nat_abs (a * b)) : (mul_nat_abs a b)⁻¹
      ... = (nat_abs 0) : {H}
      ... = nat.zero : nat_abs_of_nat nat.zero,
have H3 : (nat_abs a) = nat.zero ∨ (nat_abs b) = nat.zero, from mul.eq_zero H2,
or_of_or_of_imp_of_imp H3
  (assume H : (nat_abs a) = nat.zero, nat_abs_eq_zero H)
  (assume H : (nat_abs b) = nat.zero, nat_abs_eq_zero H)

theorem mul_cancel_left_or {a b c : ℤ} (H : a * b = a * c) : a = 0 ∨ b = c :=
have H2 : a * (b - c) = 0, by simp,
have H3 : a = 0 ∨ b - c = 0, from mul_eq_zero H2,
or_of_or_of_imp_right H3 eq_of_sub_eq_zero

theorem mul_cancel_left {a b c : ℤ} (H1 : a ≠ 0) (H2 : a * b = a * c) : b = c :=
or_resolve_right (mul_cancel_left_or H2) H1

theorem mul_cancel_right_or {a b c : ℤ} (H : b * a = c * a) : a = 0 ∨ b = c :=
mul_cancel_left_or ((H ▸ (mul.comm b a)) ▸ mul.comm c a)

theorem mul_cancel_right {a b c : ℤ} (H1 : c ≠ 0) (H2 : a * c = b * c) : a = b :=
or_resolve_right (mul_cancel_right_or H2) H1

theorem mul_ne_zero {a b : ℤ} (Ha : a ≠ 0) (Hb : b ≠ 0) : a * b ≠ 0 :=
(assume H : a * b = 0,
  or.elim (mul_eq_zero H)
    (assume H2 : a = 0, absurd H2 Ha)
    (assume H2 : b = 0, absurd H2 Hb))

theorem mul_ne_zero_left {a b : ℤ} (H : a * b ≠ 0) : a ≠ 0 :=
(assume H2 : a = 0,
  have H3 : a * b = 0, by simp,
  absurd H3 H)

theorem mul_ne_zero_right {a b : ℤ} (H : a * b ≠ 0) : b ≠ 0 :=
mul_ne_zero_left (mul.comm a b ▸ H)

theorem sub_inj_left {a b c : ℤ} (H : a - b = a - c) : b = c :=
neg.inj (add.left_cancel H)

theorem sub_inj_right {a b c : ℤ} (H : a - b = c - b) : a = c :=
add.right_cancel H

end int


/- tests -/

/- open int

eval -100
eval -(-100)

eval #int (5 + 7)
eval -5 + 7
eval 5 + -7
eval -5 + -7

eval #int 155 + 277
eval -155 + 277
eval 155 + -277
eval -155 + -277

eval #int 155 - 277
eval #int 277 - 155

eval #int 2 * 3
eval -2 * 3
eval 2 * -3
eval -2 * -3

eval 22 * 33
eval -22 * 33
eval 22 * -33
eval -22 * -33

eval #int 22 ≤ 33
eval #int 33 ≤ 22

example : #int 22 ≤ 33 := true.intro
example : #int -5 < 7 := true.intro
-/
