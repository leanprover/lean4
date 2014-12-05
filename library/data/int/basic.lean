/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: int.basic
Authors: Floris van Doorn, Jeremy Avigad

The integers, with addition, multiplication, and subtraction.

The representation of the integers is chosen to compute efficiently; see the examples in the
comments at the end of this file.

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

import data.nat.basic data.nat.order data.nat.sub data.prod algebra.relation
import algebra.binary
import tools.fake_simplifier

open prod relation
open decidable binary fake_simplifier
open eq.ops

-- TODO: move
namespace nat

theorem succ_pred_of_pos {n : ℕ} (H : n > 0) : succ (pred n) = n :=
(or.resolve_right (zero_or_succ_pred n) (ne.symm (lt_imp_ne H))⁻¹)

theorem sub_pos_of_gt {m n : ℕ} (H : n > m) : n - m > 0 :=
have H1 : n = n - m + m, from (add_sub_ge_left (lt_imp_le H))⁻¹,
have H2 : 0 + m < n - m + m, from (add.zero_left m)⁻¹ ▸ H1 ▸ H,
!add_lt_cancel_right H2

end nat

open nat

/- the type of integers -/

inductive int : Type :=
  of_nat : nat → int,
  neg_succ_of_nat : nat → int

notation `ℤ` := int
coercion [persistent] int.of_nat
definition int.of_num [coercion] (n : num) : ℤ := int.of_nat (nat.of_num n)

namespace int


/- define key functions so that they compute well -/

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
        (take n, sub_nat_nat m (succ n)))          -- b = neg_succ_of_nat n
    (take m,                                           -- a = neg_succ_of_nat m
      cases_on b
        (take n, sub_nat_nat n (succ m))           -- b = of_nat n
        (take n, neg_of_nat (succ m + succ n)))              -- b = neg_succ_of_nat n

definition mul (a b : ℤ) : ℤ :=
  cases_on a
    (take m,                                           -- a = of_nat m
      cases_on b
        (take n, of_nat (m * n))                         -- b = of_nat n
        (take n, neg_of_nat (m * succ n)))               -- b = neg_succ_of_nat n
    (take m,                                           -- a = neg_succ_of_nat m
      cases_on b
        (take n, neg_of_nat (succ m * n))              -- b = of_nat n
        (take n, of_nat (succ m * succ n)))              -- b = neg_succ_of_nat n

definition sub (a b : ℤ) : ℤ := add a (neg b)

definition nonneg (a : ℤ) : Prop := cases_on a (take n, true) (take n, false)

definition le (a b : ℤ) : Prop := nonneg (sub b a)

definition lt (a b : ℤ) : Prop := le (add a 1) b


/- notation -/

notation `-[` n `+1]` := int.neg_succ_of_nat n    -- for pretty-printing output
prefix - := int.neg
infix +  := int.add
infix *  := int.mul
infix -  := int.sub
infix <= := int.le
infix ≤  := int.le
infix <  := int.lt


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


/-
  Show int is a quotient of ordered pairs of natural numbers, with the usual
  equivalence relation.
-/

definition equiv (p q : ℕ × ℕ) : Prop :=  pr1 p + pr2 q = pr2 p + pr1 q

notation [local] p `≡` q := equiv p q

theorem equiv_refl {p : ℕ × ℕ} : p ≡ p := !add.comm

theorem equiv_symm {p q : ℕ × ℕ} (H : p ≡ q) : q ≡ p :=
calc
  pr1 q + pr2 p = pr2 p + pr1 q : !add.comm
    ... = pr1 p + pr2 q         : H⁻¹
    ... = pr2 q + pr1 p         : !add.comm

theorem equiv_trans {p q r : ℕ × ℕ} (H1 : p ≡ q) (H2 : q ≡ r) : p ≡ r :=
have H3 : pr1 p + pr2 r + pr2 q = pr2 p + pr1 r + pr2 q, from
  calc
   pr1 p + pr2 r + pr2 q = pr1 p + pr2 q + pr2 r : by simp
    ... = pr2 p + pr1 q + pr2 r                  : {H1}
    ... = pr2 p + (pr1 q + pr2 r)                : by simp
    ... = pr2 p + (pr2 q + pr1 r)                : {H2}
    ... = pr2 p + pr1 r + pr2 q                  : by simp,
show pr1 p + pr2 r = pr2 p + pr1 r, from add.cancel_right H3

theorem equiv_equiv : is_equivalence equiv :=
is_equivalence.mk @equiv_refl @equiv_symm @equiv_trans

theorem equiv_cases {p q : ℕ × ℕ} (H : equiv p q) :
    (pr1 p ≥ pr2 p ∧ pr1 q ≥ pr2 q) ∨ (pr1 p < pr2 p ∧ pr1 q < pr2 q) :=
or.elim (@le_or_gt (pr2 p) (pr1 p))
  (assume H1: pr1 p ≥ pr2 p,
    have H2 : pr2 p + pr1 q ≥ pr2 p + pr2 q, from H ▸ add_le_right H1 (pr2 q),
    or.inl (and.intro H1 (add_le_cancel_left H2)))
  (assume H1: pr1 p < pr2 p,
    have H2 : pr2 p + pr1 q < pr2 p + pr2 q, from H ▸ add_lt_right H1 (pr2 q),
    or.inr (and.intro H1 (add_lt_cancel_left H2)))

theorem equiv_of_eq {p q : ℕ × ℕ} (H : p = q) : p ≡ q := H ▸ equiv_refl

theorem eq_equiv_trans {p q r : ℕ × ℕ} (H1 : p = q) (H2 : q ≡ r) : p ≡ r := H1⁻¹ ▸ H2

theorem equiv_eq_trans {p q r : ℕ × ℕ} (H1 : p ≡ q) (H2 : q = r) : p ≡ r := H2 ▸ H1

calc_trans equiv_trans
calc_refl equiv_refl
calc_symm equiv_symm
calc_trans eq_equiv_trans
calc_trans equiv_eq_trans


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
    and.intro !equiv_refl (and.intro !equiv_refl (abstr_eq H)))
  (assume H : equiv p p ∧ equiv q q ∧ abstr p = abstr q,
    have H1 : abstr p = abstr q, from and.elim_right (and.elim_right H),
    equiv_trans (H1 ▸ equiv_symm (repr_abstr p)) (repr_abstr q))

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

theorem nat_abs_eq_zero {a : ℤ} : nat_abs a = 0 → a = 0 :=
cases_on a
  (take m, assume H : nat_abs (of_nat m) = 0, congr_arg of_nat H)
  (take m', assume H : nat_abs (neg_succ_of_nat m') = 0, absurd H (succ_ne_zero _))


/-
  Properties of the basic operations.
-/

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

theorem neg_zero : -0 = 0 := rfl

theorem neg_neg (a : ℤ) : -(-a) = a :=
have H : repr (-(-a)) = repr a, from
  (calc
    repr (-(-a)) = pneg (repr (-a)) : repr_neg
      ... = pneg (pneg (repr a)) : repr_neg
      ... = repr a : pneg_pneg),
eq_of_repr_equiv_repr (H ▸ equiv_refl)

theorem neg_inj {a b : ℤ} (H : -a = -b) : a = b :=
calc
  a = -(-a) : neg_neg
    ... = -(-b) : H
    ... = b : neg_neg

theorem neg_move {a b : ℤ} (H : -a = b) : -b = a :=
H ▸ neg_neg a

theorem nat_abs_neg (a : ℤ) : nat_abs (-a) = nat_abs a :=
calc
  nat_abs (-a) = nat_abs (abstr (repr (-a))) : abstr_repr
    ... = nat_abs (abstr (pneg (repr a))) : repr_neg
    ... = dist (pr1 (pneg (repr a))) (pr2 (pneg (repr a))) : nat_abs_abstr
    ... = dist (pr2 (pneg (repr a))) (pr1 (pneg (repr a))) : dist_comm
    ... = nat_abs (abstr (repr a)) : nat_abs_abstr
    ... = nat_abs a : abstr_repr

theorem pos_eq_neg {n m : ℕ} : n = -m → n = 0 ∧ m = 0 :=
nat.cases_on m
  (take H, and.intro (of_nat_inj H) rfl)
  (take m' H, no_confusion H)

theorem cases (a : ℤ) : (∃n : ℕ, a = of_nat n) ∨ (∃n : ℕ, a = - n) :=
cases_on a
  (take n, or.inl (exists_intro n rfl))
  (take n', or.inr (exists_intro (succ n') rfl))

theorem by_cases {P : ℤ → Prop} (a : ℤ) (H1 : ∀n : ℕ, P (of_nat n)) (H2 : ∀n : ℕ, P (-n)) :
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


/- addition -/

definition padd (p q : ℕ × ℕ) : ℕ × ℕ := map_pair2 nat.add p q

theorem repr_add (a b : ℤ) :  repr (add a b) ≡ padd (repr a) (repr b) :=
cases_on a
  (take m,
    cases_on b
      (take n, !equiv_refl)
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

theorem add_comm (a b : ℤ) : a + b = b + a :=
begin
  apply eq_of_repr_equiv_repr,
  apply equiv_trans,
  apply repr_add,
  apply equiv_symm,
  apply (eq.subst (padd_comm (repr b) (repr a))),
  apply repr_add
end

theorem add_assoc (a b c : ℤ) : a + b + c = a + (b + c) :=
have H1 [visible]: repr (a + b + c) ≡ padd (padd (repr a) (repr b)) (repr c), from
  equiv_trans (repr_add (a + b) c) (padd_congr !repr_add !equiv_refl),
have H2 [visible]: repr (a + (b + c)) ≡ padd (repr a) (padd (repr b) (repr c)), from
  equiv_trans (repr_add a (b + c)) (padd_congr !equiv_refl !repr_add),
begin
  apply eq_of_repr_equiv_repr,
  apply equiv_trans,
  apply H1,
  apply (eq.subst ((padd_assoc _ _ _)⁻¹)),
  apply equiv_symm,
  apply H2
end

theorem add_zero_right (a : ℤ) : a + 0 = a := cases_on a (take m, rfl) (take m', rfl)

theorem add_left_comm (a b c : ℤ) : a + (b + c) = b + (a + c) :=
left_comm add_comm add_assoc a b c

theorem add_right_comm (a b c : ℤ) : a + b + c = a + c + b :=
right_comm add_comm add_assoc a b c

theorem add_zero_left (a : ℤ) : 0 + a = a :=
add_comm a 0 ▸ add_zero_right a

theorem padd_pneg (p : ℕ × ℕ) : padd p (pneg p) ≡ (0, 0) :=
show pr1 p + pr2 p + 0 = pr2 p + pr1 p + 0, from !add.comm ▸ rfl

theorem padd_padd_pneg (p q : ℕ × ℕ) : padd (padd p q) (pneg q) ≡ p :=
show pr1 p + pr1 q + pr2 q + pr2 p = pr2 p + pr2 q + pr1 q + pr1 p, by simp

theorem add_inverse_right (a : ℤ) : a + -a = 0 :=
have H : repr (a + -a) ≡ repr 0, from
  calc
    repr (a + -a) ≡ padd (repr a) (repr (neg a)) : repr_add
      ... = padd (repr a) (pneg (repr a)) : repr_neg
      ... ≡ repr 0 : padd_pneg,
eq_of_repr_equiv_repr H

theorem add_inverse_left (a : ℤ) : -a + a = 0 :=
add_comm a (-a) ▸ add_inverse_right a

theorem pneg_padd_distr (p q : ℕ × ℕ) : pneg (padd p q) = padd (pneg p) (pneg q) := rfl

theorem neg_add_distr (a b : ℤ) : -(a + b) = -a + -b :=
eq_of_repr_equiv_repr
  (calc
    repr (-(a + b)) = pneg (repr (a + b)) : repr_neg
      ... ≡ pneg (padd (repr a) (repr b)) : pneg_congr (!repr_add)
      ... = padd (pneg (repr a)) (pneg (repr b)) : pneg_padd_distr
      ... = padd (repr (-a)) (pneg (repr b)) : repr_neg
      ... = padd (repr (-a)) (repr (-b)) : repr_neg
      ... ≡ repr (-a + -b) : equiv_symm (!repr_add))
                -- TODO: should calc reorient this for us?

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

/- subtraction -/

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
    ... = (pr1 q * pr1 p + pr2 q * pr2 p, pr1 q * pr2 p + pr2 q * pr1 p) : add.comm

theorem mul_comm (a b : ℤ) : a * b = b * a :=
eq_of_repr_equiv_repr
  ((calc
    repr (a * b) = pmul (repr a) (repr b) : repr_mul
      ... = pmul (repr b) (repr a) : pmul_comm
      ... = repr (b * a) : repr_mul) ▸ !equiv_refl)

theorem pmul_assoc (p q r: ℕ × ℕ) : pmul (pmul p q) r = pmul p (pmul q r) :=
by simp

theorem mul_assoc (a b c : ℤ) : (a * b) * c = a * (b * c) :=
eq_of_repr_equiv_repr
  ((calc
    repr (a * b * c) = pmul (repr (a * b)) (repr c) : repr_mul
      ... = pmul (pmul (repr a) (repr b)) (repr c) : repr_mul
      ... = pmul (repr a) (pmul (repr b) (repr c)) : pmul_assoc
      ... = pmul (repr a) (repr (b * c)) : repr_mul
      ... = repr (a * (b * c)) : repr_mul) ▸ !equiv_refl)

theorem mul_left_comm : ∀a b c : ℤ, a * (b * c) = b * (a * c) :=
left_comm mul_comm mul_assoc

theorem mul_right_comm : ∀a b c : ℤ, a * b * c = a * c * b :=
right_comm mul_comm mul_assoc

theorem mul_zero_right (a : ℤ) : a * 0 = 0 :=
eq_of_repr_equiv_repr (equiv_of_eq
  ((calc
    repr (a * 0) = pmul (repr a) (repr 0) : repr_mul
      ... = (0, 0) : by simp)))

theorem mul_zero_left (a : ℤ) : 0 * a = 0 :=
mul_comm a 0 ▸ mul_zero_right a

theorem mul_one_right (a : ℤ) : a * 1 = a :=
eq_of_repr_equiv_repr (equiv_of_eq
  ((calc
    repr (a * 1) = pmul (repr a) (repr 1) : repr_mul
      ... = (pr1 (repr a), pr2 (repr a)) : by simp
      ... = repr a : prod.eta)))

theorem mul_one_left (a : ℤ) : 1 * a = a :=
mul_comm a 1 ▸ mul_one_right a

theorem mul_neg_right (a b : ℤ) : a * -b = -(a * b) :=
let a1 := pr1 (repr a), a2 := pr2 (repr a), b1 := pr1 (repr b), b2 := pr2 (repr b) in
eq_of_repr_equiv_repr (equiv_of_eq
  ((calc
    repr (a * -b) = pmul (repr a) (repr (-b)) : repr_mul
      ... = pmul (repr a) (pneg (repr b)) : repr_neg
      ... = (a1 * b2 + a2 * b1, a1 * b1 + a2 * b2) : rfl
      ... = pneg (pmul (repr a) (repr b)) : rfl
      ... = pneg (repr (a * b)) : repr_mul
      ... = repr (-(a * b)) : repr_neg)))

theorem mul_neg_left (a b : ℤ) : -a * b = -(a * b) :=
mul_comm b a ▸ mul_comm b (-a) ▸ mul_neg_right b a

-- add_rewrite mul_neg_right mul_neg_left

theorem mul_neg_neg (a b : ℤ) : -a * -b = a * b :=
by simp

theorem mul_right_distr (a b c : ℤ) : (a + b) * c = a * c + b * c :=
eq_of_repr_equiv_repr
  (calc
    repr ((a + b) * c) = pmul (repr (a + b)) (repr c) : repr_mul
      ... ≡ pmul (padd (repr a) (repr b)) (repr c) : pmul_congr !repr_add equiv_refl
      ... = padd (pmul (repr a) (repr c)) (pmul (repr b) (repr c)) : by simp
      ... = padd (repr (a * c)) (pmul (repr b) (repr c)) : {(repr_mul a c)⁻¹}
      ... = padd (repr (a * c)) (repr (b * c)) : repr_mul
      ... ≡ repr (a * c + b * c) : equiv_symm !repr_add)

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

-- add_rewrite mul_zero_left mul_zero_right mul_one_right mul_one_left
-- add_rewrite mul_comm mul_assoc mul_left_comm
-- add_rewrite mul_distr_right mul_distr_left mul_of_nat mul_sub_distr_left mul_sub_distr_right

theorem mul_eq_zero {a b : ℤ} (H : a * b = 0) : a = 0 ∨ b = 0 :=
have H2 : (nat_abs a) * (nat_abs b) = 0, from
  calc
    (nat_abs a) * (nat_abs b) = (nat_abs (a * b)) : (mul_nat_abs a b)⁻¹
      ... = (nat_abs 0) : {H}
      ... = 0 : nat_abs_of_nat 0,
have H3 : (nat_abs a) = 0 ∨ (nat_abs b) = 0, from mul.eq_zero H2,
or.imp_or H3
  (assume H : (nat_abs a) = 0, nat_abs_eq_zero H)
  (assume H : (nat_abs b) = 0, nat_abs_eq_zero H)

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
