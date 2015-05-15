/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jeremy Avigad

The integers, with addition, multiplication, and subtraction. The representation of the integers is
chosen to compute efficiently.

To faciliate proving things about these operations, we show that the integers are a quotient of
ℕ × ℕ with the usual equivalence relation, ≡, and functions

  abstr : ℕ × ℕ → ℤ
  repr : ℤ → ℕ × ℕ

satisfying:

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
| of_nat : nat → int
| neg_succ_of_nat : nat → int

notation `ℤ` := int
attribute int.of_nat [coercion]
definition int.of_num [coercion] [reducible] [constructor] (n : num) : ℤ :=
int.of_nat (nat.of_num n)

namespace int

/- definitions of basic functions -/

definition neg_of_nat (m : ℕ) : ℤ :=
nat.cases_on m 0 (take m', neg_succ_of_nat m')

definition sub_nat_nat (m n : ℕ) : ℤ :=
nat.cases_on (n - m)
  (of_nat (m - n))                                     -- m ≥ n
  (take k, neg_succ_of_nat k)                          -- m < n, and n - m = succ k

definition neg (a : ℤ) : ℤ :=
  int.cases_on a
    (take m,                                           -- a = of_nat m
      nat.cases_on m 0 (take m', neg_succ_of_nat m'))
    (take m, of_nat (succ m))                          -- a = neg_succ_of_nat m

definition add (a b : ℤ) : ℤ :=
  int.cases_on a
    (take m,                                           -- a = of_nat m
      int.cases_on b
        (take n, of_nat (m + n))                         -- b = of_nat n
        (take n, sub_nat_nat m (succ n)))                -- b = neg_succ_of_nat n
    (take m,                                           -- a = neg_succ_of_nat m
      int.cases_on b
        (take n, sub_nat_nat n (succ m))                 -- b = of_nat n
        (take n, neg_of_nat (succ m + succ n)))          -- b = neg_succ_of_nat n

definition mul (a b : ℤ) : ℤ :=
  int.cases_on a
    (take m,                                           -- a = of_nat m
      int.cases_on b
        (take n, of_nat (m * n))                         -- b = of_nat n
        (take n, neg_of_nat (m * succ n)))               -- b = neg_succ_of_nat n
    (take m,                                           -- a = neg_succ_of_nat m
      int.cases_on b
        (take n, neg_of_nat (succ m * n))                -- b = of_nat n
        (take n, of_nat (succ m * succ n)))              -- b = neg_succ_of_nat n

/- notation -/

notation `-[` n `+1]` := int.neg_succ_of_nat n    -- for pretty-printing output
prefix - := int.neg
infix +  := int.add
infix *  := int.mul

/- some basic functions and properties -/

theorem of_nat.inj {m n : ℕ} (H : of_nat m = of_nat n) : m = n :=
by injection H; assumption

theorem neg_succ_of_nat.inj {m n : ℕ} (H : neg_succ_of_nat m = neg_succ_of_nat n) : m = n :=
by injection H; assumption

theorem neg_succ_of_nat_eq (n : ℕ) : -[n +1] = -(n + 1) := rfl

definition has_decidable_eq [instance] : decidable_eq ℤ :=
take a b,
int.cases_on a
  (take m,
    int.cases_on b
      (take n,
        if H : m = n then inl (congr_arg of_nat H) else inr (take H1, H (of_nat.inj H1)))
      (take n', inr (by contradiction)))
  (take m',
    int.cases_on b
      (take n, inr (by contradiction))
      (take n',
        (if H : m' = n' then inl (congr_arg neg_succ_of_nat H) else
            inr (take H1, H (neg_succ_of_nat.inj H1)))))

theorem of_nat_add (n m : nat) : of_nat (n + m) = of_nat n + of_nat m := rfl

theorem of_nat_succ (n : ℕ) : of_nat (succ n) = of_nat n + 1 := rfl

theorem of_nat_mul (n m : ℕ) : of_nat (n * m) = of_nat n * of_nat m := rfl

theorem sub_nat_nat_of_ge {m n : ℕ} (H : m ≥ n) : sub_nat_nat m n = of_nat (m - n) :=
have H1 : n - m = 0, from sub_eq_zero_of_le H,
calc
  sub_nat_nat m n = nat.cases_on 0 (of_nat (m - n)) _ : H1 ▸ rfl
    ... = of_nat (m - n) : rfl

section
local attribute sub_nat_nat [reducible]
theorem sub_nat_nat_of_lt {m n : ℕ} (H : m < n) :
  sub_nat_nat m n = neg_succ_of_nat (pred (n - m)) :=
have H1 : n - m = succ (pred (n - m)), from (succ_pred_of_pos (sub_pos_of_lt H))⁻¹,
calc
  sub_nat_nat m n = nat.cases_on (succ (pred (n - m))) (of_nat (m - n))
        (take k, neg_succ_of_nat k) : H1 ▸ rfl
    ... = neg_succ_of_nat (pred (n - m)) : rfl
end

definition nat_abs (a : ℤ) : ℕ := int.cases_on a (take n, n) (take n', succ n')

theorem nat_abs_of_nat (n : ℕ) : nat_abs (of_nat n) = n := rfl

theorem nat_abs_eq_zero {a : ℤ} : nat_abs a = 0 → a = 0 :=
int.cases_on a
  (take m, assume H : nat_abs (of_nat m) = 0, congr_arg of_nat H)
  (take m', assume H : nat_abs (neg_succ_of_nat m') = 0, absurd H (succ_ne_zero _))

/- int is a quotient of ordered pairs of natural numbers -/

protected definition equiv (p q : ℕ × ℕ) : Prop :=  pr1 p + pr2 q = pr2 p + pr1 q

local infix `≡` := int.equiv

protected theorem equiv.refl [refl] {p : ℕ × ℕ} : p ≡ p := !add.comm

protected theorem equiv.symm [symm] {p q : ℕ × ℕ} (H : p ≡ q) : q ≡ p :=
calc
  pr1 q + pr2 p = pr2 p + pr1 q : !add.comm
    ... = pr1 p + pr2 q         : H⁻¹
    ... = pr2 q + pr1 p         : !add.comm

protected theorem equiv.trans [trans] {p q r : ℕ × ℕ} (H1 : p ≡ q) (H2 : q ≡ r) : p ≡ r :=
have H3 : pr1 p + pr2 r + pr2 q = pr2 p + pr1 r + pr2 q, from
  calc
   pr1 p + pr2 r + pr2 q = pr1 p + pr2 q + pr2 r : by simp
    ... = pr2 p + pr1 q + pr2 r                  : {H1}
    ... = pr2 p + (pr1 q + pr2 r)                : by simp
    ... = pr2 p + (pr2 q + pr1 r)                : {H2}
    ... = pr2 p + pr1 r + pr2 q                  : by simp,
show pr1 p + pr2 r = pr2 p + pr1 r, from add.cancel_right H3

protected theorem equiv_equiv : is_equivalence int.equiv :=
is_equivalence.mk @equiv.refl @equiv.symm @equiv.trans

protected theorem equiv_cases {p q : ℕ × ℕ} (H : int.equiv p q) :
    (pr1 p ≥ pr2 p ∧ pr1 q ≥ pr2 q) ∨ (pr1 p < pr2 p ∧ pr1 q < pr2 q) :=
or.elim (@le_or_gt (pr2 p) (pr1 p))
  (assume H1: pr1 p ≥ pr2 p,
    have H2 : pr2 p + pr1 q ≥ pr2 p + pr2 q, from H ▸ add_le_add_right H1 (pr2 q),
    or.inl (and.intro H1 (le_of_add_le_add_left H2)))
  (assume H1: pr1 p < pr2 p,
    have H2 : pr2 p + pr1 q < pr2 p + pr2 q, from H ▸ add_lt_add_right H1 (pr2 q),
    or.inr (and.intro H1 (lt_of_add_lt_add_left H2)))

protected theorem equiv_of_eq {p q : ℕ × ℕ} (H : p = q) : p ≡ q := H ▸ equiv.refl

/- the representation and abstraction functions -/

definition abstr (a : ℕ × ℕ) : ℤ := sub_nat_nat (pr1 a) (pr2 a)

theorem abstr_of_ge {p : ℕ × ℕ} (H : pr1 p ≥ pr2 p) : abstr p = of_nat (pr1 p - pr2 p) :=
sub_nat_nat_of_ge H

theorem abstr_of_lt {p : ℕ × ℕ} (H : pr1 p < pr2 p) :
  abstr p = neg_succ_of_nat (pred (pr2 p - pr1 p)) :=
sub_nat_nat_of_lt H

definition repr (a : ℤ) : ℕ × ℕ := int.cases_on a (take m, (m, 0)) (take m, (0, succ m))

theorem abstr_repr (a : ℤ) : abstr (repr a) = a :=
int.cases_on a (take m, (sub_nat_nat_of_ge (zero_le m))) (take m, rfl)

theorem repr_sub_nat_nat (m n : ℕ) : repr (sub_nat_nat m n) ≡ (m, n) :=
or.elim (@le_or_gt n m)
  (take H : m ≥ n,
    have H1 : repr (sub_nat_nat m n) = (m - n, 0), from sub_nat_nat_of_ge H ▸ rfl,
    H1⁻¹ ▸
      (calc
        m - n + n = m : sub_add_cancel H
          ... = 0 + m : zero_add))
  (take H : m < n,
    have H1 : repr (sub_nat_nat m n) = (0, succ (pred (n - m))), from sub_nat_nat_of_lt H ▸ rfl,
    H1⁻¹ ▸
      (calc
        0 + n = n : zero_add
          ... = n - m + m : sub_add_cancel (le_of_lt H)
          ... = succ (pred (n - m)) + m : (succ_pred_of_pos (sub_pos_of_lt H))⁻¹))

theorem repr_abstr (p : ℕ × ℕ) : repr (abstr p) ≡ p :=
!prod.eta ▸ !repr_sub_nat_nat

theorem abstr_eq {p q : ℕ × ℕ} (Hequiv : p ≡ q) : abstr p = abstr q :=
or.elim (int.equiv_cases Hequiv)
  (assume H2,
    have H3 : pr1 p ≥ pr2 p, from and.elim_left H2,
    have H4 : pr1 q ≥ pr2 q, from and.elim_right H2,
    have H5 : pr1 p = pr1 q - pr2 q + pr2 p, from
      calc
        pr1 p = pr1 p + pr2 q - pr2 q : add_sub_cancel
          ... = pr2 p + pr1 q - pr2 q : Hequiv
          ... = pr2 p + (pr1 q - pr2 q) : add_sub_assoc H4
          ... = pr1 q - pr2 q + pr2 p : add.comm,
    have H6 : pr1 p - pr2 p = pr1 q - pr2 q, from
      calc
        pr1 p - pr2 p = pr1 q - pr2 q + pr2 p - pr2 p : H5
                  ... = pr1 q - pr2 q                 : add_sub_cancel,
    abstr_of_ge H3 ⬝ congr_arg of_nat H6 ⬝ (abstr_of_ge H4)⁻¹)
  (assume H2,
    have H3 : pr1 p < pr2 p, from and.elim_left H2,
    have H4 : pr1 q < pr2 q, from and.elim_right H2,
    have H5 : pr2 p = pr2 q - pr1 q + pr1 p, from
      calc
        pr2 p = pr2 p + pr1 q - pr1 q : add_sub_cancel
          ... = pr1 p + pr2 q - pr1 q : Hequiv
          ... = pr1 p + (pr2 q - pr1 q) : add_sub_assoc (le_of_lt H4)
          ... = pr2 q - pr1 q + pr1 p : add.comm,
    have H6 : pr2 p - pr1 p = pr2 q - pr1 q, from
      calc
        pr2 p - pr1 p = pr2 q - pr1 q + pr1 p - pr1 p : H5
                  ... = pr2 q - pr1 q                 : add_sub_cancel,
    abstr_of_lt H3 ⬝ congr_arg neg_succ_of_nat (congr_arg pred H6)⬝ (abstr_of_lt H4)⁻¹)

theorem equiv_iff (p q : ℕ × ℕ) : (p ≡ q) ↔ ((p ≡ p) ∧ (q ≡ q) ∧ (abstr p = abstr q)) :=
iff.intro
  (assume H : int.equiv p q,
    and.intro !equiv.refl (and.intro !equiv.refl (abstr_eq H)))
  (assume H : int.equiv p p ∧ int.equiv q q ∧ abstr p = abstr q,
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

section
local attribute abstr [reducible]
local attribute dist [reducible]
theorem nat_abs_abstr (p : ℕ × ℕ) : nat_abs (abstr p) = dist (pr1 p) (pr2 p) :=
let m := pr1 p, n := pr2 p in
or.elim (@le_or_gt n m)
  (assume H : m ≥ n,
    calc
      nat_abs (abstr (m, n)) = nat_abs (of_nat (m - n)) : int.abstr_of_ge H
                         ... = dist m n                 : dist_eq_sub_of_ge H)
  (assume H : m < n,
    calc
      nat_abs (abstr (m, n)) = nat_abs (neg_succ_of_nat (pred (n - m))) : int.abstr_of_lt H
        ... = succ (pred (n - m)) : rfl
        ... = n - m               : succ_pred_of_pos (sub_pos_of_lt H)
        ... = dist m n            : dist_eq_sub_of_le (le_of_lt H))
end

theorem cases_of_nat (a : ℤ) : (∃n : ℕ, a = of_nat n) ∨ (∃n : ℕ, a = - of_nat n) :=
int.cases_on a
  (take n, or.inl (exists.intro n rfl))
  (take n', or.inr (exists.intro (succ n') rfl))

theorem cases_of_nat_succ (a : ℤ) : (∃n : ℕ, a = of_nat n) ∨ (∃n : ℕ, a = - (of_nat (succ n))) :=
int.cases_on a (take m, or.inl (exists.intro _ rfl)) (take m, or.inr (exists.intro _ rfl))

theorem by_cases_of_nat {P : ℤ → Prop} (a : ℤ)
    (H1 : ∀n : ℕ, P (of_nat n)) (H2 : ∀n : ℕ, P (- of_nat n)) :
  P a :=
or.elim (cases_of_nat a)
  (assume H, obtain (n : ℕ) (H3 : a = n), from H, H3⁻¹ ▸ H1 n)
  (assume H, obtain (n : ℕ) (H3 : a = -n), from H, H3⁻¹ ▸ H2 n)

theorem by_cases_of_nat_succ {P : ℤ → Prop} (a : ℤ)
    (H1 : ∀n : ℕ, P (of_nat n)) (H2 : ∀n : ℕ, P (- of_nat (succ n))) :
  P a :=
or.elim (cases_of_nat_succ a)
  (assume H, obtain (n : ℕ) (H3 : a = n), from H, H3⁻¹ ▸ H1 n)
  (assume H, obtain (n : ℕ) (H3 : a = -(succ n)), from H, H3⁻¹ ▸ H2 n)

/-
   int is a ring
-/

/- addition -/

definition padd (p q : ℕ × ℕ) : ℕ × ℕ := (pr1 p + pr1 q, pr2 p + pr2 q)

theorem repr_add (a b : ℤ) :  repr (add a b) ≡ padd (repr a) (repr b) :=
int.cases_on a
  (take m,
    int.cases_on b
      (take n, !equiv.refl)
      (take n',
        have H1 : int.equiv (repr (add (of_nat m) (neg_succ_of_nat n'))) (m, succ n'),
          from !repr_sub_nat_nat,
        have H2 : padd (repr (of_nat m)) (repr (neg_succ_of_nat n')) = (m, 0 + succ n'),
          from rfl,
        (!zero_add ▸ H2)⁻¹ ▸ H1))
  (take m',
    int.cases_on b
      (take n,
        have H1 : int.equiv (repr (add (neg_succ_of_nat m') (of_nat n))) (n, succ m'),
          from !repr_sub_nat_nat,
        have H2 : padd (repr (neg_succ_of_nat m')) (repr (of_nat n)) = (0 + n, succ m'),
          from rfl,
        (!zero_add ▸ H2)⁻¹ ▸ H1)
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
  apply eq.subst (padd_comm (repr b) (repr a)),
  apply repr_add
end

theorem add.assoc (a b c : ℤ) : a + b + c = a + (b + c) :=
assert H1 : repr (a + b + c) ≡ padd (padd (repr a) (repr b)) (repr c), from
  equiv.trans (repr_add (a + b) c) (padd_congr !repr_add !equiv.refl),
assert H2 : repr (a + (b + c)) ≡ padd (repr a) (padd (repr b) (repr c)), from
  equiv.trans (repr_add a (b + c)) (padd_congr !equiv.refl !repr_add),
begin
  apply eq_of_repr_equiv_repr,
  apply equiv.trans,
  apply H1,
  apply eq.subst (padd_assoc _ _ _)⁻¹,
  apply equiv.symm,
  apply H2
end

theorem add_zero (a : ℤ) : a + 0 = a := int.cases_on a (take m, rfl) (take m', rfl)

theorem zero_add (a : ℤ) : 0 + a = a := add.comm a 0 ▸ add_zero a

/- negation -/

definition pneg (p : ℕ × ℕ) : ℕ × ℕ := (pr2 p, pr1 p)

-- note: this is =, not just ≡
theorem repr_neg (a : ℤ) : repr (- a) = pneg (repr a) :=
int.cases_on a
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
    ... = dist (pr2 (pneg (repr a))) (pr1 (pneg (repr a))) : dist.comm
    ... = nat_abs (abstr (repr a)) : nat_abs_abstr
    ... = nat_abs a : abstr_repr

theorem padd_pneg (p : ℕ × ℕ) : padd p (pneg p) ≡ (0, 0) :=
show pr1 p + pr2 p + 0 = pr2 p + pr1 p + 0, from !nat.add.comm ▸ rfl

theorem padd_padd_pneg (p q : ℕ × ℕ) : padd (padd p q) (pneg q) ≡ p :=
show pr1 p + pr1 q + pr2 q + pr2 p = pr2 p + pr2 q + pr1 q + pr1 p, from by simp

theorem add.left_inv (a : ℤ) : -a + a = 0 :=
have H : repr (-a + a) ≡ repr 0, from
  calc
    repr (-a + a) ≡ padd (repr (neg a)) (repr a) : repr_add
      ... = padd (pneg (repr a)) (repr a) : repr_neg
      ... ≡ repr 0 : padd_pneg,
eq_of_repr_equiv_repr H

/- nat abs -/

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
have H3 : pabs (padd (repr a) (repr b)) ≤ pabs (repr a) + pabs (repr b),
  from !dist_add_add_le_add_dist_dist,
H⁻¹ ▸ H1⁻¹ ▸ H2⁻¹ ▸ H3

section
local attribute nat_abs [reducible]
theorem mul_nat_abs (a b : ℤ) : nat_abs (a * b) = #nat (nat_abs a) * (nat_abs b) :=
int.cases_on a
  (take m,
    int.cases_on b
      (take n, rfl)
      (take n', !nat_abs_neg ▸ rfl))
  (take m',
    int.cases_on b
      (take n, !nat_abs_neg ▸ rfl)
      (take n', rfl))
end

/- multiplication -/

definition pmul (p q : ℕ × ℕ) : ℕ × ℕ :=
  (pr1 p * pr1 q + pr2 p * pr2 q, pr1 p * pr2 q + pr2 p * pr1 q)

theorem repr_neg_of_nat (m : ℕ) : repr (neg_of_nat m) = (0, m) :=
nat.cases_on m rfl (take m', rfl)

-- note: we have =, not just ≡
theorem repr_mul (a b : ℤ) :  repr (mul a b) = pmul (repr a) (repr b) :=
int.cases_on a
  (take m,
    int.cases_on b
      (take n,
        (calc
          pmul (repr m) (repr n) = (m * n + 0 * 0, m * 0 + 0 * n) : rfl
            ... = (m * n + 0 * 0, m * 0 + 0) : zero_mul)⁻¹)
      (take n',
        (calc
          pmul (repr m) (repr (neg_succ_of_nat n')) =
              (m * 0 + 0 * succ n', m * succ n' + 0 * 0) : rfl
            ... = (m * 0 + 0, m * succ n' + 0 * 0) : zero_mul
            ... = repr (mul m (neg_succ_of_nat n')) : repr_neg_of_nat)⁻¹))
  (take m',
    int.cases_on b
      (take n,
        (calc
          pmul (repr (neg_succ_of_nat m')) (repr n) =
              (0 * n + succ m' * 0, 0 * 0 + succ m' * n) : rfl
            ... = (0 + succ m' * 0, 0 * 0 + succ m' * n) : zero_mul
            ... = (0 + succ m' * 0, succ m' * n) : {!nat.zero_add}
            ... = repr (mul (neg_succ_of_nat m') n) : repr_neg_of_nat)⁻¹)
      (take n',
        (calc
          pmul (repr (neg_succ_of_nat m')) (repr (neg_succ_of_nat n')) =
              (0 + succ m' * succ n', 0 * succ n') : rfl
            ... = (succ m' * succ n', 0 * succ n') : nat.zero_add
            ... = (succ m' * succ n', 0) : zero_mul
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

theorem mul_one (a : ℤ) : a * 1 = a :=
eq_of_repr_equiv_repr (int.equiv_of_eq
  ((calc
    repr (a * 1) = pmul (repr a) (repr 1) : repr_mul
      ... = (pr1 (repr a), pr2 (repr a)) : by simp
      ... = repr a : prod.eta)))

theorem one_mul (a : ℤ) : 1 * a = a :=
mul.comm a 1 ▸ mul_one a

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
show false, from succ_ne_zero 0 ((of_nat.inj H)⁻¹)

theorem eq_zero_or_eq_zero_of_mul_eq_zero {a b : ℤ} (H : a * b = 0) : a = 0 ∨ b = 0 :=
have H2 : (nat_abs a) * (nat_abs b) = nat.zero, from
  calc
    (nat_abs a) * (nat_abs b) = (nat_abs (a * b)) : (mul_nat_abs a b)⁻¹
      ... = (nat_abs 0) : {H}
      ... = nat.zero : nat_abs_of_nat nat.zero,
have H3 : (nat_abs a) = nat.zero ∨ (nat_abs b) = nat.zero,
  from eq_zero_or_eq_zero_of_mul_eq_zero H2,
or_of_or_of_imp_of_imp H3
  (assume H : (nat_abs a) = nat.zero, nat_abs_eq_zero H)
  (assume H : (nat_abs b) = nat.zero, nat_abs_eq_zero H)

section migrate_algebra
  open [classes] algebra

  protected definition integral_domain [reducible] : algebra.integral_domain int :=
  ⦃algebra.integral_domain,
    add            := add,
    add_assoc      := add.assoc,
    zero           := zero,
    zero_add       := zero_add,
    add_zero       := add_zero,
    neg            := neg,
    add_left_inv   := add.left_inv,
    add_comm       := add.comm,
    mul            := mul,
    mul_assoc      := mul.assoc,
    one            := (of_num 1),
    one_mul        := one_mul,
    mul_one        := mul_one,
    left_distrib   := mul.left_distrib,
    right_distrib  := mul.right_distrib,
    mul_comm       := mul.comm,
    eq_zero_or_eq_zero_of_mul_eq_zero := @eq_zero_or_eq_zero_of_mul_eq_zero⦄

  local attribute int.integral_domain [instance]
  definition sub (a b : ℤ) : ℤ := algebra.sub a b
  infix - := int.sub
  definition dvd (a b : ℤ) : Prop := algebra.dvd a b
  notation a ∣ b := dvd a b

  migrate from algebra with int
  replacing sub → sub, dvd → dvd
end migrate_algebra

/- additional properties -/

theorem of_nat_sub {m n : ℕ} (H : #nat m ≥ n) : of_nat (#nat m - n) = of_nat m - of_nat n :=
have H1 : m = (#nat m - n + n), from (nat.sub_add_cancel H)⁻¹,
have H2 : m = (#nat m - n) + n, from congr_arg of_nat H1,
(sub_eq_of_eq_add H2)⁻¹

theorem neg_succ_of_nat_eq' (m : ℕ) : -[m +1] = -m - 1 :=
by rewrite [neg_succ_of_nat_eq, of_nat_add, neg_add]

definition succ (a : ℤ) := a + (nat.succ zero)
definition pred (a : ℤ) := a - (nat.succ zero)
theorem pred_succ (a : ℤ) : pred (succ a) = a := !sub_add_cancel
theorem succ_pred (a : ℤ) : succ (pred a) = a := !add_sub_cancel
theorem neg_succ (a : ℤ) : -succ a = pred (-a) :=
by rewrite [↑succ,neg_add]
theorem succ_neg_succ (a : ℤ) : succ (-succ a) = -a :=
by rewrite [neg_succ,succ_pred]
theorem neg_pred (a : ℤ) : -pred a = succ (-a) :=
by rewrite [↑pred,neg_sub,sub_eq_add_neg,add.comm]
theorem pred_neg_pred (a : ℤ) : pred (-pred a) = -a :=
by rewrite [neg_pred,pred_succ]

theorem pred_nat_succ (n : ℕ) : pred (nat.succ n) = n := pred_succ n
theorem neg_nat_succ (n : ℕ) : -nat.succ n = pred (-n) := !neg_succ
theorem succ_neg_nat_succ (n : ℕ) : succ (-nat.succ n) = -n := !succ_neg_succ

definition rec_nat_on [unfold-c 2] {P : ℤ → Type} (z : ℤ) (H0 : P 0)
  (Hsucc : Π⦃n : ℕ⦄, P n → P (succ n)) (Hpred : Π⦃n : ℕ⦄, P (-n) → P (-nat.succ n)) : P z :=
int.rec_on z (λn, nat.rec_on n H0 Hsucc) (λn, nat.rec_on n (Hpred H0) (λm H, Hpred H))

--the only computation rule of rec_nat_on which is not definitional
theorem rec_nat_on_neg {P : ℤ → Type} (n : nat) (H0 : P zero)
  (Hsucc : Π⦃n : nat⦄, P n → P (succ n)) (Hpred : Π⦃n : nat⦄, P (-n) → P (-nat.succ n))
  : rec_nat_on (-nat.succ n) H0 Hsucc Hpred = Hpred (rec_nat_on (-n) H0 Hsucc Hpred) :=
nat.rec_on n rfl (λn H, rfl)

end int
