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

Ported from standard library
-/
import types.nat.sub algebra.relation types.prod

open core nat decidable prod relation prod

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

definition of_nat.inj {m n : ℕ} (H : of_nat m = of_nat n) : m = n :=
by injection H; assumption

definition neg_succ_of_nat.inj {m n : ℕ} (H : neg_succ_of_nat m = neg_succ_of_nat n) : m = n :=
by injection H; assumption

definition neg_succ_of_nat_eq (n : ℕ) : -[n +1] = -(n + 1) := rfl

definition has_decidable_eq [instance] : decidable_eq ℤ :=
take a b,
int.cases_on a
  (take m,
    int.cases_on b
      (take n,
        if H : m = n then inl (ap of_nat H) else inr (take H1, H (of_nat.inj H1)))
      (take n', inr (by contradiction)))
  (take m',
    int.cases_on b
      (take n, inr (by contradiction))
      (take n',
        (if H : m' = n' then inl (ap neg_succ_of_nat H) else
            inr (take H1, H (neg_succ_of_nat.inj H1)))))

definition of_nat_add_of_nat (n m : nat) : of_nat n + of_nat m = #nat n + m := rfl

definition of_nat_succ (n : ℕ) : of_nat (succ n) = of_nat n + 1 := rfl

definition of_nat_mul_of_nat (n m : ℕ) : of_nat n * of_nat m = n * m := rfl

definition sub_nat_nat_of_ge {m n : ℕ} (H : m ≥ n) : sub_nat_nat m n = of_nat (m - n) :=
have H1 : n - m = 0, from sub_eq_zero_of_le H,
calc
  sub_nat_nat m n = nat.cases_on 0 (of_nat (m - n)) _ : H1 ▸ rfl
    ... = of_nat (m - n) : rfl

section
local attribute sub_nat_nat [reducible]
definition sub_nat_nat_of_lt {m n : ℕ} (H : m < n) :
  sub_nat_nat m n = neg_succ_of_nat (pred (n - m)) :=
have H1 : n - m = succ (pred (n - m)), from (succ_pred_of_pos (sub_pos_of_lt H))⁻¹,
calc
  sub_nat_nat m n = nat.cases_on (succ (pred (n - m))) (of_nat (m - n))
        (take k, neg_succ_of_nat k) : H1 ▸ rfl
    ... = neg_succ_of_nat (pred (n - m)) : rfl
end

definition nat_abs (a : ℤ) : ℕ := int.cases_on a (take n, n) (take n', succ n')

definition nat_abs_of_nat (n : ℕ) : nat_abs (of_nat n) = n := rfl

definition nat_abs_eq_zero {a : ℤ} : nat_abs a = 0 → a = 0 :=
int.cases_on a
  (take m, assume H : nat_abs (of_nat m) = 0, ap of_nat H)
  (take m', assume H : nat_abs (neg_succ_of_nat m') = 0, absurd H (succ_ne_zero _))

/- int is a quotient of ordered pairs of natural numbers -/

definition int_equiv (p q : ℕ × ℕ) : Type₀ :=  pr1 p + pr2 q = pr2 p + pr1 q

local infix `≡` := int_equiv

protected theorem int_equiv.refl [refl] {p : ℕ × ℕ} : p ≡ p := !add.comm

protected theorem int_equiv.symm [symm] {p q : ℕ × ℕ} (H : p ≡ q) : q ≡ p :=
calc
  pr1 q + pr2 p = pr2 p + pr1 q : !add.comm
    ... = pr1 p + pr2 q         : H⁻¹
    ... = pr2 q + pr1 p         : !add.comm

protected theorem int_equiv.trans [trans] {p q r : ℕ × ℕ} (H1 : p ≡ q) (H2 : q ≡ r) : p ≡ r :=
add.cancel_right (calc
   pr1 p + pr2 r + pr2 q = pr1 p + pr2 q + pr2 r : add.right_comm
    ... = pr2 p + pr1 q + pr2 r                  : {H1}
    ... = pr2 p + (pr1 q + pr2 r)                : add.assoc
    ... = pr2 p + (pr2 q + pr1 r)                : {H2}
    ... = pr2 p + pr2 q + pr1 r                  : add.assoc
    ... = pr2 p + pr1 r + pr2 q                  : add.right_comm)

definition int_equiv_int_equiv : is_equivalence int_equiv :=
is_equivalence.mk @int_equiv.refl @int_equiv.symm @int_equiv.trans

definition int_equiv_cases {p q : ℕ × ℕ} (H : int_equiv p q) :
    (pr1 p ≥ pr2 p × pr1 q ≥ pr2 q) ⊎ (pr1 p < pr2 p × pr1 q < pr2 q) :=
sum.rec_on (@le_or_gt (pr2 p) (pr1 p))
  (assume H1: pr1 p ≥ pr2 p,
    have H2 : pr2 p + pr1 q ≥ pr2 p + pr2 q, from H ▸ add_le_add_right H1 (pr2 q),
    sum.inl (pair H1 (le_of_add_le_add_left H2)))
  (assume H1: pr1 p < pr2 p,
    have H2 : pr2 p + pr1 q < pr2 p + pr2 q, from H ▸ add_lt_add_right H1 (pr2 q),
    sum.inr (pair H1 (lt_of_add_lt_add_left H2)))

definition int_equiv_of_eq {p q : ℕ × ℕ} (H : p = q) : p ≡ q := H ▸ int_equiv.refl

/- the representation and abstraction functions -/

definition abstr (a : ℕ × ℕ) : ℤ := sub_nat_nat (pr1 a) (pr2 a)

definition abstr_of_ge {p : ℕ × ℕ} (H : pr1 p ≥ pr2 p) : abstr p = of_nat (pr1 p - pr2 p) :=
sub_nat_nat_of_ge H

definition abstr_of_lt {p : ℕ × ℕ} (H : pr1 p < pr2 p) :
  abstr p = neg_succ_of_nat (pred (pr2 p - pr1 p)) :=
sub_nat_nat_of_lt H

definition repr (a : ℤ) : ℕ × ℕ := int.cases_on a (take m, (m, 0)) (take m, (0, succ m))

definition abstr_repr (a : ℤ) : abstr (repr a) = a :=
int.cases_on a (take m, (sub_nat_nat_of_ge (zero_le m))) (take m, rfl)

definition repr_sub_nat_nat (m n : ℕ) : repr (sub_nat_nat m n) ≡ (m, n) :=
sum.rec_on (@le_or_gt n m)
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
          ... = succ (pred (n - m)) + m : (succ_pred_of_pos (sub_pos_of_lt H))⁻¹ᵖ))

definition repr_abstr (p : ℕ × ℕ) : repr (abstr p) ≡ p :=
!prod.eta ▸ !repr_sub_nat_nat

definition abstr_eq {p q : ℕ × ℕ} (Hint_equiv : p ≡ q) : abstr p = abstr q :=
sum.rec_on (int_equiv_cases Hint_equiv)
  (assume H2,
    have H3 : pr1 p ≥ pr2 p, from prod.pr1 H2,
    have H4 : pr1 q ≥ pr2 q, from prod.pr2 H2,
    have H5 : pr1 p = pr1 q - pr2 q + pr2 p, from
      calc
        pr1 p = pr1 p + pr2 q - pr2 q : add_sub_cancel
          ... = pr2 p + pr1 q - pr2 q : by rewrite [↑int_equiv at Hint_equiv,Hint_equiv]
          ... = pr2 p + (pr1 q - pr2 q) : add_sub_assoc H4
          ... = pr1 q - pr2 q + pr2 p : add.comm,
    have H6 : pr1 p - pr2 p = pr1 q - pr2 q, from
      calc
        pr1 p - pr2 p = pr1 q - pr2 q + pr2 p - pr2 p : H5
                  ... = pr1 q - pr2 q                 : add_sub_cancel,
    abstr_of_ge H3 ⬝ ap of_nat H6 ⬝ (abstr_of_ge H4)⁻¹)
  (assume H2,
    have H3 : pr1 p < pr2 p, from prod.pr1 H2,
    have H4 : pr1 q < pr2 q, from prod.pr2 H2,
    have H5 : pr2 p = pr2 q - pr1 q + pr1 p, from
      calc
        pr2 p = pr2 p + pr1 q - pr1 q : add_sub_cancel
          ... = pr1 p + pr2 q - pr1 q : by rewrite [↑int_equiv at Hint_equiv,Hint_equiv]
          ... = pr1 p + (pr2 q - pr1 q) : add_sub_assoc (le_of_lt H4)
          ... = pr2 q - pr1 q + pr1 p : add.comm,
    have H6 : pr2 p - pr1 p = pr2 q - pr1 q, from
      calc
        pr2 p - pr1 p = pr2 q - pr1 q + pr1 p - pr1 p : H5
                  ... = pr2 q - pr1 q                 : add_sub_cancel,
    abstr_of_lt H3 ⬝ ap neg_succ_of_nat (ap pred H6)⬝ (abstr_of_lt H4)⁻¹)

definition int_equiv_iff (p q : ℕ × ℕ) : (p ≡ q) ↔ ((p ≡ p) × (q ≡ q) × (abstr p = abstr q)) :=
iff.intro
  (assume H : int_equiv p q,
    pair !int_equiv.refl (pair !int_equiv.refl (abstr_eq H)))
  (assume H : int_equiv p p × int_equiv q q × abstr p = abstr q,
    have H1 : abstr p = abstr q, from prod.pr2 (prod.pr2 H),
    int_equiv.trans (H1 ▸ int_equiv.symm (repr_abstr p)) (repr_abstr q))

definition eq_abstr_of_int_equiv_repr {a : ℤ} {p : ℕ × ℕ} (Hint_equiv : repr a ≡ p) : a = abstr p :=
calc
  a = abstr (repr a) : abstr_repr
   ... = abstr p : abstr_eq Hint_equiv

definition eq_of_repr_int_equiv_repr {a b : ℤ} (H : repr a ≡ repr b) : a = b :=
calc
  a = abstr (repr a) : abstr_repr
    ... = abstr (repr b) : abstr_eq H
    ... = b : abstr_repr

section
local attribute abstr [reducible]
local attribute dist [reducible]
definition nat_abs_abstr (p : ℕ × ℕ) : nat_abs (abstr p) = dist (pr1 p) (pr2 p) :=
let m := pr1 p, n := pr2 p in
sum.rec_on (@le_or_gt n m)
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

definition cases_of_nat (a : ℤ) : (Σn : ℕ, a = of_nat n) ⊎ (Σn : ℕ, a = - of_nat n) :=
int.cases_on a
  (take n, sum.inl (sigma.mk n rfl))
  (take n', sum.inr (sigma.mk (succ n') rfl))

definition cases_of_nat_succ (a : ℤ) : (Σn : ℕ, a = of_nat n) ⊎ (Σn : ℕ, a = - (of_nat (succ n))) :=
int.cases_on a (take m, sum.inl (sigma.mk _ rfl)) (take m, sum.inr (sigma.mk _ rfl))

definition by_cases_of_nat {P : ℤ → Type} (a : ℤ)
    (H1 : Πn : ℕ, P (of_nat n)) (H2 : Πn : ℕ, P (- of_nat n)) :
  P a :=
sum.rec_on (cases_of_nat a)
  (assume H, obtain (n : ℕ) (H3 : a = n), from H, H3⁻¹ ▸ H1 n)
  (assume H, obtain (n : ℕ) (H3 : a = -n), from H, H3⁻¹ ▸ H2 n)

definition by_cases_of_nat_succ {P : ℤ → Type} (a : ℤ)
    (H1 : Πn : ℕ, P (of_nat n)) (H2 : Πn : ℕ, P (- of_nat (succ n))) :
  P a :=
sum.rec_on (cases_of_nat_succ a)
  (assume H, obtain (n : ℕ) (H3 : a = n), from H, H3⁻¹ ▸ H1 n)
  (assume H, obtain (n : ℕ) (H3 : a = -(succ n)), from H, H3⁻¹ ▸ H2 n)

/-
   int is a ring
-/

/- addition -/

definition padd (p q : ℕ × ℕ) : ℕ × ℕ := (pr1 p + pr1 q, pr2 p + pr2 q)

definition repr_add (a b : ℤ) :  repr (add a b) ≡ padd (repr a) (repr b) :=
int.cases_on a
  (take m,
    int.cases_on b
      (take n, !int_equiv.refl)
      (take n',
        have H1 : int_equiv (repr (add (of_nat m) (neg_succ_of_nat n'))) (m, succ n'),
          from !repr_sub_nat_nat,
        have H2 : padd (repr (of_nat m)) (repr (neg_succ_of_nat n')) = (m, 0 + succ n'),
          from rfl,
        (!zero_add ▸ H2)⁻¹ ▸ H1))
  (take m',
    int.cases_on b
      (take n,
        have H1 : int_equiv (repr (add (neg_succ_of_nat m') (of_nat n))) (n, succ m'),
          from !repr_sub_nat_nat,
        have H2 : padd (repr (neg_succ_of_nat m')) (repr (of_nat n)) = (0 + n, succ m'),
          from rfl,
        (!zero_add ▸ H2)⁻¹ ▸ H1)
       (take n',!repr_sub_nat_nat))

definition padd_congr {p p' q q' : ℕ × ℕ} (Ha : p ≡ p') (Hb : q ≡ q') : padd p q ≡ padd p' q' :=
calc pr1 p + pr1 q + (pr2 p' + pr2 q')
        = pr1 p + pr2 p' + (pr1 q + pr2 q') : add.comm4
    ... = pr2 p + pr1 p' + (pr1 q + pr2 q') : {Ha}
    ... = pr2 p + pr1 p' + (pr2 q + pr1 q') : {Hb}
    ... = pr2 p + pr2 q + (pr1 p' + pr1 q') : add.comm4

definition padd_comm (p q : ℕ × ℕ) : padd p q = padd q p :=
calc
  padd p q = (pr1 p + pr1 q, pr2 p + pr2 q) : rfl
    ... = (pr1 q + pr1 p, pr2 p + pr2 q) : add.comm
    ... = (pr1 q + pr1 p, pr2 q + pr2 p) : add.comm
    ... = padd q p : rfl

definition padd_assoc (p q r : ℕ × ℕ) : padd (padd p q) r = padd p (padd q r) :=
calc
  padd (padd p q) r = (pr1 p + pr1 q + pr1 r, pr2 p + pr2 q + pr2 r) : rfl
    ... = (pr1 p + (pr1 q + pr1 r), pr2 p + pr2 q + pr2 r) : add.assoc
    ... = (pr1 p + (pr1 q + pr1 r), pr2 p + (pr2 q + pr2 r)) : add.assoc
    ... = padd p (padd q r) : rfl

definition add.comm (a b : ℤ) : a + b = b + a :=
begin
  apply eq_of_repr_int_equiv_repr,
  apply int_equiv.trans,
  apply repr_add,
  apply int_equiv.symm,
  apply eq.subst (padd_comm (repr b) (repr a)),
  apply repr_add
end

definition add.assoc (a b c : ℤ) : a + b + c = a + (b + c) :=
assert H1 : repr (a + b + c) ≡ padd (padd (repr a) (repr b)) (repr c), from
  int_equiv.trans (repr_add (a + b) c) (padd_congr !repr_add !int_equiv.refl),
assert H2 : repr (a + (b + c)) ≡ padd (repr a) (padd (repr b) (repr c)), from
  int_equiv.trans (repr_add a (b + c)) (padd_congr !int_equiv.refl !repr_add),
begin
  apply eq_of_repr_int_equiv_repr,
  apply int_equiv.trans,
  apply H1,
  apply eq.subst (padd_assoc _ _ _)⁻¹,
  apply int_equiv.symm,
  apply H2
end

definition add_zero (a : ℤ) : a + 0 = a := int.cases_on a (take m, rfl) (take m', rfl)

definition zero_add (a : ℤ) : 0 + a = a := add.comm a 0 ▸ add_zero a

/- negation -/

definition pneg (p : ℕ × ℕ) : ℕ × ℕ := (pr2 p, pr1 p)

-- note: this is =, not just ≡
definition repr_neg (a : ℤ) : repr (- a) = pneg (repr a) :=
int.cases_on a
  (take m,
    nat.cases_on m rfl (take m', rfl))
  (take m', rfl)

definition pneg_congr {p p' : ℕ × ℕ} (H : p ≡ p') : pneg p ≡ pneg p' := inverse H

definition pneg_pneg (p : ℕ × ℕ) : pneg (pneg p) = p := !prod.eta

definition nat_abs_neg (a : ℤ) : nat_abs (-a) = nat_abs a :=
calc
  nat_abs (-a) = nat_abs (abstr (repr (-a))) : abstr_repr
    ... = nat_abs (abstr (pneg (repr a))) : repr_neg
    ... = dist (pr1 (pneg (repr a))) (pr2 (pneg (repr a))) : nat_abs_abstr
    ... = dist (pr2 (pneg (repr a))) (pr1 (pneg (repr a))) : dist.comm
    ... = nat_abs (abstr (repr a)) : nat_abs_abstr
    ... = nat_abs a : abstr_repr

definition padd_pneg (p : ℕ × ℕ) : padd p (pneg p) ≡ (0, 0) :=
show pr1 p + pr2 p + 0 = pr2 p + pr1 p + 0, from !nat.add.comm ▸ rfl

definition padd_padd_pneg (p q : ℕ × ℕ) : padd (padd p q) (pneg q) ≡ p :=
calc      pr1 p + pr1 q + pr2 q + pr2 p
        = pr1 p + (pr1 q + pr2 q) + pr2 p : nat.add.assoc
    ... = pr1 p + (pr1 q + pr2 q + pr2 p) : nat.add.assoc
    ... = pr1 p + (pr2 q + pr1 q + pr2 p) : nat.add.comm
    ... = pr1 p + (pr2 q + pr2 p + pr1 q) : add.right_comm
    ... = pr1 p + (pr2 p + pr2 q + pr1 q) : nat.add.comm
    ... = pr2 p + pr2 q + pr1 q + pr1 p   : nat.add.comm

definition add.left_inv (a : ℤ) : -a + a = 0 :=
have H : repr (-a + a) ≡ repr 0, from
  calc
    repr (-a + a) ≡ padd (repr (neg a)) (repr a) : repr_add
      ... = padd (pneg (repr a)) (repr a) : repr_neg
      ... ≡ repr 0 : padd_pneg,
eq_of_repr_int_equiv_repr H

/- nat abs -/

definition pabs (p : ℕ × ℕ) : ℕ := dist (pr1 p) (pr2 p)

definition pabs_congr {p q : ℕ × ℕ} (H : p ≡ q) : pabs p = pabs q :=
calc
  pabs p = nat_abs (abstr p) : nat_abs_abstr
    ... = nat_abs (abstr q) : abstr_eq H
    ... = pabs q : nat_abs_abstr

definition nat_abs_eq_pabs_repr (a : ℤ) : nat_abs a = pabs (repr a) :=
calc
  nat_abs a = nat_abs (abstr (repr a)) : abstr_repr
    ... = pabs (repr a) : nat_abs_abstr

definition nat_abs_add_le (a b : ℤ) : nat_abs (a + b) ≤ nat_abs a + nat_abs b :=
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
definition mul_nat_abs (a b : ℤ) : nat_abs (a * b) = #nat (nat_abs a) * (nat_abs b) :=
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

definition repr_neg_of_nat (m : ℕ) : repr (neg_of_nat m) = (0, m) :=
nat.cases_on m rfl (take m', rfl)

-- note: we have =, not just ≡
definition repr_mul (a b : ℤ) :  repr (mul a b) = pmul (repr a) (repr b) :=
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

definition int_equiv_mul_prep {xa ya xb yb xn yn xm ym : ℕ}
  (H1 : xa + yb = ya + xb) (H2 : xn + ym = yn + xm)
: xa * xn + ya * yn + (xb * ym + yb * xm) = xa * yn + ya * xn + (xb * xm + yb * ym) :=
nat.add.cancel_right (calc
            xa*xn+ya*yn + (xb*ym+yb*xm) + (yb*xn+xb*yn + (xb*xn+yb*yn))
          = xa*xn+ya*yn + (yb*xn+xb*yn) + (xb*ym+yb*xm + (xb*xn+yb*yn)) : add.comm4
      ... = xa*xn+ya*yn + (yb*xn+xb*yn) + (xb*xn+yb*yn + (xb*ym+yb*xm)) : nat.add.comm
      ... = xa*xn+yb*xn + (ya*yn+xb*yn) + (xb*xn+xb*ym + (yb*yn+yb*xm)) : !congr_arg2 add.comm4 add.comm4
      ... = ya*xn+xb*xn + (xa*yn+yb*yn) + (xb*yn+xb*xm + (yb*xn+yb*ym))
          : by rewrite[-+mul.left_distrib,-+mul.right_distrib]; exact H1 ▸ H2 ▸ rfl
      ... = ya*xn+xa*yn + (xb*xn+yb*yn) + (xb*yn+yb*xn + (xb*xm+yb*ym)) : !congr_arg2 add.comm4 add.comm4
      ... = xa*yn+ya*xn + (xb*xn+yb*yn) + (yb*xn+xb*yn + (xb*xm+yb*ym)) : !nat.add.comm ▸ !nat.add.comm ▸ rfl
      ... = xa*yn+ya*xn + (yb*xn+xb*yn) + (xb*xn+yb*yn + (xb*xm+yb*ym)) : add.comm4
      ... = xa*yn+ya*xn + (yb*xn+xb*yn) + (xb*xm+yb*ym + (xb*xn+yb*yn)) : nat.add.comm
      ... = xa*yn+ya*xn + (xb*xm+yb*ym) + (yb*xn+xb*yn + (xb*xn+yb*yn)) : add.comm4)

definition pmul_congr {p p' q q' : ℕ × ℕ} (H1 : p ≡ p') (H2 : q ≡ q') : pmul p q ≡ pmul p' q' :=
int_equiv_mul_prep H1 H2

definition pmul_comm (p q : ℕ × ℕ) : pmul p q = pmul q p :=
calc
  (pr1 p * pr1 q + pr2 p * pr2 q, pr1 p * pr2 q + pr2 p * pr1 q) =
      (pr1 q * pr1 p + pr2 p * pr2 q, pr1 p * pr2 q + pr2 p * pr1 q) : mul.comm
    ... = (pr1 q * pr1 p + pr2 q * pr2 p, pr1 p * pr2 q + pr2 p * pr1 q) : mul.comm
    ... = (pr1 q * pr1 p + pr2 q * pr2 p, pr2 q * pr1 p + pr2 p * pr1 q) : mul.comm
    ... = (pr1 q * pr1 p + pr2 q * pr2 p, pr2 q * pr1 p + pr1 q * pr2 p) : mul.comm
    ... = (pr1 q * pr1 p + pr2 q * pr2 p, pr1 q * pr2 p + pr2 q * pr1 p) : nat.add.comm

definition mul.comm (a b : ℤ) : a * b = b * a :=
eq_of_repr_int_equiv_repr
  ((calc
    repr (a * b) = pmul (repr a) (repr b) : repr_mul
      ... = pmul (repr b) (repr a) : pmul_comm
      ... = repr (b * a) : repr_mul) ▸ !int_equiv.refl)

private theorem pmul_assoc_prep {p1 p2 q1 q2 r1 r2 : ℕ} :
  ((p1*q1+p2*q2)*r1+(p1*q2+p2*q1)*r2, (p1*q1+p2*q2)*r2+(p1*q2+p2*q1)*r1) =
   (p1*(q1*r1+q2*r2)+p2*(q1*r2+q2*r1), p1*(q1*r2+q2*r1)+p2*(q1*r1+q2*r2)) :=
begin
   rewrite[+mul.left_distrib,+mul.right_distrib,*mul.assoc],
   rewrite (@add.comm4 (p1 * (q1 * r1)) (p2 * (q2 * r1)) (p1 * (q2 * r2)) (p2 * (q1 * r2))),
   rewrite (nat.add.comm (p2 * (q2 * r1)) (p2 * (q1 * r2))),
   rewrite (@add.comm4 (p1 * (q1 * r2)) (p2 * (q2 * r2)) (p1 * (q2 * r1)) (p2 * (q1 * r1))),
   rewrite (nat.add.comm (p2 * (q2 * r2)) (p2 * (q1 * r1)))
end

definition pmul_assoc (p q r: ℕ × ℕ) : pmul (pmul p q) r = pmul p (pmul q r) :=
pmul_assoc_prep

definition mul.assoc (a b c : ℤ) : (a * b) * c = a * (b * c) :=
eq_of_repr_int_equiv_repr
  ((calc
    repr (a * b * c) = pmul (repr (a * b)) (repr c) : repr_mul
      ... = pmul (pmul (repr a) (repr b)) (repr c) : repr_mul
      ... = pmul (repr a) (pmul (repr b) (repr c)) : pmul_assoc
      ... = pmul (repr a) (repr (b * c)) : repr_mul
      ... = repr (a * (b * c)) : repr_mul) ▸ !int_equiv.refl)

set_option pp.coercions true

definition mul_one (a : ℤ) : a * 1 = a :=
eq_of_repr_int_equiv_repr (int_equiv_of_eq
  ((calc
    repr (a * 1) = pmul (repr a) (repr 1) : repr_mul
      ... = (pr1 (repr a), pr2 (repr a))  : by unfold [pmul, repr]; krewrite [*mul_zero, *mul_one, *nat.add_zero, *nat.zero_add]
      ... = repr a : prod.eta)))

definition one_mul (a : ℤ) : 1 * a = a :=
mul.comm a 1 ▸ mul_one a

private theorem mul_distrib_prep {a1 a2 b1 b2 c1 c2 : ℕ} :
 ((a1+b1)*c1+(a2+b2)*c2, (a1+b1)*c2+(a2+b2)*c1) =
 (a1*c1+a2*c2+(b1*c1+b2*c2), a1*c2+a2*c1+(b1*c2+b2*c1)) :=
by rewrite[+mul.right_distrib] ⬝ (!congr_arg2 !add.comm4 !add.comm4)

definition mul.right_distrib (a b c : ℤ) : (a + b) * c = a * c + b * c :=
eq_of_repr_int_equiv_repr
  (calc
    repr ((a + b) * c) = pmul (repr (a + b)) (repr c) : repr_mul
      ... ≡ pmul (padd (repr a) (repr b)) (repr c) : pmul_congr !repr_add int_equiv.refl
      ... = padd (pmul (repr a) (repr c)) (pmul (repr b) (repr c)) : mul_distrib_prep
      ... = padd (repr (a * c)) (pmul (repr b) (repr c)) : {(repr_mul a c)⁻¹}
      ... = padd (repr (a * c)) (repr (b * c)) : repr_mul
      ... ≡ repr (a * c + b * c) : int_equiv.symm !repr_add)

definition mul.left_distrib (a b c : ℤ) : a * (b + c) = a * b + a * c :=
calc
  a * (b + c) = (b + c) * a : mul.comm a (b + c)
    ... = b * a + c * a : mul.right_distrib b c a
    ... = a * b + c * a : {mul.comm b a}
    ... = a * b + a * c : {mul.comm c a}

definition zero_ne_one : (0 : int) ≠ 1 :=
assume H : 0 = 1,
show empty, from succ_ne_zero 0 ((of_nat.inj H)⁻¹)

definition eq_zero_or_eq_zero_of_mul_eq_zero {a b : ℤ} (H : a * b = 0) : a = 0 ⊎ b = 0 :=
have H2 : (nat_abs a) * (nat_abs b) = nat.zero, from
  calc
    (nat_abs a) * (nat_abs b) = (nat_abs (a * b)) : (mul_nat_abs a b)⁻¹
      ... = (nat_abs 0) : {H}
      ... = nat.zero : nat_abs_of_nat nat.zero,
have H3 : (nat_abs a) = nat.zero ⊎ (nat_abs b) = nat.zero,
  from eq_zero_or_eq_zero_of_mul_eq_zero H2,
sum_of_sum_of_imp_of_imp H3
  (assume H : (nat_abs a) = nat.zero, nat_abs_eq_zero H)
  (assume H : (nat_abs b) = nat.zero, nat_abs_eq_zero H)

section
  open [classes] algebra

  protected definition integral_domain [instance] [reducible] : algebra.integral_domain int :=
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
    eq_zero_or_eq_zero_of_mul_eq_zero := @eq_zero_or_eq_zero_of_mul_eq_zero,
    is_hset_carrier := is_hset_of_decidable_eq⦄
end

/- instantiate ring theorems to int -/

section port_algebra
  open [classes] algebra
  definition mul.left_comm : Πa b c : ℤ, a * (b * c) = b * (a * c) := algebra.mul.left_comm
  definition mul.right_comm : Πa b c : ℤ, (a * b) * c = (a * c) * b := algebra.mul.right_comm
  definition add.left_comm : Πa b c : ℤ, a + (b + c) = b + (a + c) := algebra.add.left_comm
  definition add.right_comm : Πa b c : ℤ, (a + b) + c = (a + c) + b := algebra.add.right_comm
  definition add.left_cancel : Π{a b c : ℤ}, a + b = a + c → b = c := @algebra.add.left_cancel _ _
  definition add.right_cancel : Π{a b c : ℤ}, a + b = c + b → a = c := @algebra.add.right_cancel _ _
  definition neg_add_cancel_left : Πa b : ℤ, -a + (a + b) = b := algebra.neg_add_cancel_left
  definition neg_add_cancel_right : Πa b : ℤ, a + -b + b = a := algebra.neg_add_cancel_right
  definition neg_eq_of_add_eq_zero : Π{a b : ℤ}, a + b = 0 → -a = b :=
    @algebra.neg_eq_of_add_eq_zero _ _
  definition neg_zero : -0 = 0 := algebra.neg_zero
  definition neg_neg : Πa : ℤ, -(-a) = a := algebra.neg_neg
  definition neg.inj : Π{a b : ℤ}, -a = -b → a = b := @algebra.neg.inj _ _
  definition neg_eq_neg_iff_eq : Πa b : ℤ, -a = -b ↔ a = b := algebra.neg_eq_neg_iff_eq
  definition neg_eq_zero_iff_eq_zero : Πa : ℤ, -a = 0 ↔ a = 0 := algebra.neg_eq_zero_iff_eq_zero
  definition eq_neg_of_eq_neg : Π{a b : ℤ}, a = -b → b = -a := @algebra.eq_neg_of_eq_neg _ _
  definition eq_neg_iff_eq_neg : Π{a b : ℤ}, a = -b ↔ b = -a := @algebra.eq_neg_iff_eq_neg _ _
  definition add.right_inv : Πa : ℤ, a + -a = 0 := algebra.add.right_inv
  definition add_neg_cancel_left : Πa b : ℤ, a + (-a + b) = b := algebra.add_neg_cancel_left
  definition add_neg_cancel_right : Πa b : ℤ, a + b + -b = a := algebra.add_neg_cancel_right
  definition neg_add_rev : Πa b : ℤ, -(a + b) = -b + -a := algebra.neg_add_rev
  definition eq_add_neg_of_add_eq : Π{a b c : ℤ}, a + c = b → a = b + -c :=
    @algebra.eq_add_neg_of_add_eq _ _
  definition eq_neg_add_of_add_eq : Π{a b c : ℤ}, b + a = c → a = -b + c :=
    @algebra.eq_neg_add_of_add_eq _ _
  definition neg_add_eq_of_eq_add : Π{a b c : ℤ}, b = a + c → -a + b = c :=
    @algebra.neg_add_eq_of_eq_add _ _
  definition add_neg_eq_of_eq_add : Π{a b c : ℤ}, a = c + b → a + -b = c :=
    @algebra.add_neg_eq_of_eq_add _ _
  definition eq_add_of_add_neg_eq : Π{a b c : ℤ}, a + -c = b → a = b + c :=
    @algebra.eq_add_of_add_neg_eq _ _
  definition eq_add_of_neg_add_eq : Π{a b c : ℤ}, -b + a = c → a = b + c :=
    @algebra.eq_add_of_neg_add_eq _ _
  definition add_eq_of_eq_neg_add : Π{a b c : ℤ}, b = -a + c → a + b = c :=
    @algebra.add_eq_of_eq_neg_add _ _
  definition add_eq_of_eq_add_neg : Π{a b c : ℤ}, a = c + -b → a + b = c :=
    @algebra.add_eq_of_eq_add_neg _ _
  definition add_eq_iff_eq_neg_add : Πa b c : ℤ, a + b = c ↔ b = -a + c :=
    @algebra.add_eq_iff_eq_neg_add _ _
  definition add_eq_iff_eq_add_neg : Πa b c : ℤ, a + b = c ↔ a = c + -b :=
    @algebra.add_eq_iff_eq_add_neg _ _
  definition sub (a b : ℤ) : ℤ := algebra.sub a b
  infix - := int.sub
  definition sub_eq_add_neg : Πa b : ℤ, a - b = a + -b := algebra.sub_eq_add_neg
  definition sub_self : Πa : ℤ, a - a = 0 := algebra.sub_self
  definition sub_add_cancel : Πa b : ℤ, a - b + b = a := algebra.sub_add_cancel
  definition add_sub_cancel : Πa b : ℤ, a + b - b = a := algebra.add_sub_cancel
  definition eq_of_sub_eq_zero : Π{a b : ℤ}, a - b = 0 → a = b := @algebra.eq_of_sub_eq_zero _ _
  definition eq_iff_sub_eq_zero : Πa b : ℤ, a = b ↔ a - b = 0 := algebra.eq_iff_sub_eq_zero
  definition zero_sub : Πa : ℤ, 0 - a = -a := algebra.zero_sub
  definition sub_zero : Πa : ℤ, a - 0 = a := algebra.sub_zero
  definition sub_neg_eq_add : Πa b : ℤ, a - (-b) = a + b := algebra.sub_neg_eq_add
  definition neg_sub : Πa b : ℤ, -(a - b) = b - a := algebra.neg_sub
  definition add_sub : Πa b c : ℤ, a + (b - c) = a + b - c := algebra.add_sub
  definition sub_add_eq_sub_sub_swap : Πa b c : ℤ, a - (b + c) = a - c - b :=
    algebra.sub_add_eq_sub_sub_swap
  definition sub_eq_iff_eq_add : Πa b c : ℤ, a - b = c ↔ a = c + b := algebra.sub_eq_iff_eq_add
  definition eq_sub_iff_add_eq : Πa b c : ℤ, a = b - c ↔ a + c = b := algebra.eq_sub_iff_add_eq
  definition eq_iff_eq_of_sub_eq_sub : Π{a b c d : ℤ}, a - b = c - d → (a = b ↔ c = d) :=
    @algebra.eq_iff_eq_of_sub_eq_sub _ _
  definition eq_sub_of_add_eq : Π{a b c : ℤ}, a + c = b → a = b - c := @algebra.eq_sub_of_add_eq _ _
  definition sub_eq_of_eq_add : Π{a b c : ℤ}, a = c + b → a - b = c := @algebra.sub_eq_of_eq_add _ _
  definition eq_add_of_sub_eq : Π{a b c : ℤ}, a - c = b → a = b + c := @algebra.eq_add_of_sub_eq _ _
  definition add_eq_of_eq_sub : Π{a b c : ℤ}, a = c - b → a + b = c := @algebra.add_eq_of_eq_sub _ _
  definition sub_add_eq_sub_sub : Πa b c : ℤ, a - (b + c) = a - b - c := algebra.sub_add_eq_sub_sub
  definition neg_add_eq_sub : Πa b : ℤ, -a + b = b - a := algebra.neg_add_eq_sub
  definition neg_add : Πa b : ℤ, -(a + b) = -a + -b := algebra.neg_add
  definition sub_add_eq_add_sub : Πa b c : ℤ, a - b + c = a + c - b := algebra.sub_add_eq_add_sub
  definition sub_sub_ : Πa b c : ℤ, a - b - c = a - (b + c) := algebra.sub_sub
  definition add_sub_add_left_eq_sub : Πa b c : ℤ, (c + a) - (c + b) = a - b :=
    algebra.add_sub_add_left_eq_sub
  definition eq_sub_of_add_eq' : Π{a b c : ℤ}, c + a = b → a = b - c := @algebra.eq_sub_of_add_eq' _ _
  definition sub_eq_of_eq_add' : Π{a b c : ℤ}, a = b + c → a - b = c := @algebra.sub_eq_of_eq_add' _ _
  definition eq_add_of_sub_eq' : Π{a b c : ℤ}, a - b = c → a = b + c := @algebra.eq_add_of_sub_eq' _ _
  definition add_eq_of_eq_sub' : Π{a b c : ℤ}, b = c - a → a + b = c := @algebra.add_eq_of_eq_sub' _ _
  definition ne_zero_of_mul_ne_zero_right : Π{a b : ℤ}, a * b ≠ 0 → a ≠ 0 :=
    @algebra.ne_zero_of_mul_ne_zero_right _ _
  definition ne_zero_of_mul_ne_zero_left : Π{a b : ℤ}, a * b ≠ 0 → b ≠ 0 :=
    @algebra.ne_zero_of_mul_ne_zero_left _ _
  definition dvd (a b : ℤ) : Type₀ := algebra.dvd a b
  notation a ∣ b := dvd a b
  definition dvd.intro : Π{a b c : ℤ} (H : a * c = b), a ∣ b := @algebra.dvd.intro _ _
  definition dvd.intro_left : Π{a b c : ℤ} (H : c * a = b), a ∣ b := @algebra.dvd.intro_left _ _
  definition exists_eq_mul_right_of_dvd : Π{a b : ℤ} (H : a ∣ b), Σc, b = a * c :=
    @algebra.exists_eq_mul_right_of_dvd _ _
  definition dvd.elim : Π{P : Type} {a b : ℤ} (H₁ : a ∣ b) (H₂ : Πc, b = a * c → P), P :=
    @algebra.dvd.elim _ _
  definition exists_eq_mul_left_of_dvd : Π{a b : ℤ} (H : a ∣ b), Σc, b = c * a :=
    @algebra.exists_eq_mul_left_of_dvd _ _
  definition dvd.elim_left : Π{P : Type} {a b : ℤ} (H₁ : a ∣ b) (H₂ : Πc, b = c * a → P), P :=
    @algebra.dvd.elim_left _ _
  definition dvd.refl : Πa : ℤ, (a ∣ a) := algebra.dvd.refl
  definition dvd.trans : Π{a b c : ℤ} (H₁ : a ∣ b) (H₂ : b ∣ c), a ∣ c := @algebra.dvd.trans _ _
  definition eq_zero_of_zero_dvd : Π{a : ℤ} (H : 0 ∣ a), a = 0 := @algebra.eq_zero_of_zero_dvd _ _
  definition dvd_zero : Πa : ℤ, a ∣ 0 := algebra.dvd_zero
  definition one_dvd : Πa : ℤ, 1 ∣ a := algebra.one_dvd
  definition dvd_mul_right : Πa b : ℤ, a ∣ a * b := algebra.dvd_mul_right
  definition dvd_mul_left : Πa b : ℤ, a ∣ b * a := algebra.dvd_mul_left
  definition dvd_mul_of_dvd_left : Π{a b : ℤ} (H : a ∣ b) (c : ℤ), a ∣ b * c :=
    @algebra.dvd_mul_of_dvd_left _ _
  definition dvd_mul_of_dvd_right : Π{a b : ℤ} (H : a ∣ b) (c : ℤ), a ∣ c * b :=
    @algebra.dvd_mul_of_dvd_right _ _
  definition mul_dvd_mul : Π{a b c d : ℤ}, a ∣ b → c ∣ d → a * c ∣ b * d :=
    @algebra.mul_dvd_mul _ _
  definition dvd_of_mul_right_dvd : Π{a b c : ℤ}, a * b ∣ c → a ∣ c :=
    @algebra.dvd_of_mul_right_dvd _ _
  definition dvd_of_mul_left_dvd : Π{a b c : ℤ}, a * b ∣ c → b ∣ c :=
    @algebra.dvd_of_mul_left_dvd _ _
  definition dvd_add : Π{a b c : ℤ}, a ∣ b → a ∣ c → a ∣ b + c := @algebra.dvd_add _ _
  definition zero_mul : Πa : ℤ, 0 * a = 0 := algebra.zero_mul
  definition mul_zero : Πa : ℤ, a * 0 = 0 := algebra.mul_zero
  definition neg_mul_eq_neg_mul : Πa b : ℤ, -(a * b) = -a * b := algebra.neg_mul_eq_neg_mul
  definition neg_mul_eq_mul_neg : Πa b : ℤ, -(a * b) = a * -b := algebra.neg_mul_eq_mul_neg
  definition neg_mul_neg : Πa b : ℤ, -a * -b = a * b := algebra.neg_mul_neg
  definition neg_mul_comm : Πa b : ℤ, -a * b = a * -b := algebra.neg_mul_comm
  definition neg_eq_neg_one_mul : Πa : ℤ, -a = -1 * a := algebra.neg_eq_neg_one_mul
  definition mul_sub_left_distrib : Πa b c : ℤ, a * (b - c) = a * b - a * c :=
    algebra.mul_sub_left_distrib
  definition mul_sub_right_distrib : Πa b c : ℤ, (a - b) * c = a * c - b * c :=
    algebra.mul_sub_right_distrib
  definition mul_add_eq_mul_add_iff_sub_mul_add_eq :
      Πa b c d e : ℤ, a * e + c = b * e + d ↔ (a - b) * e + c = d :=
    algebra.mul_add_eq_mul_add_iff_sub_mul_add_eq
  definition mul_self_sub_mul_self_eq : Πa b : ℤ, a * a - b * b = (a + b) * (a - b) :=
    algebra.mul_self_sub_mul_self_eq
  definition mul_self_sub_one_eq : Πa : ℤ, a * a - 1 = (a + 1) * (a - 1) :=
    algebra.mul_self_sub_one_eq
  definition dvd_neg_iff_dvd : Πa b : ℤ, a ∣ -b ↔ a ∣ b := algebra.dvd_neg_iff_dvd
  definition neg_dvd_iff_dvd : Πa b : ℤ, -a ∣ b ↔ a ∣ b := algebra.neg_dvd_iff_dvd
  definition dvd_sub : Πa b c : ℤ, a ∣ b → a ∣ c → a ∣ b - c := algebra.dvd_sub
  definition mul_ne_zero : Π{a b : ℤ}, a ≠ 0 → b ≠ 0 → a * b ≠ 0 := @algebra.mul_ne_zero _ _
  definition eq_of_mul_eq_mul_right : Π{a b c : ℤ}, a ≠ 0 → b * a = c * a → b = c :=
    @algebra.eq_of_mul_eq_mul_right _ _
  definition eq_of_mul_eq_mul_left : Π{a b c : ℤ}, a ≠ 0 → a * b = a * c → b = c :=
    @algebra.eq_of_mul_eq_mul_left _ _
  definition mul_self_eq_mul_self_iff : Πa b : ℤ, a * a = b * b ↔ a = b ⊎ a = -b :=
    algebra.mul_self_eq_mul_self_iff
  definition mul_self_eq_one_iff : Πa : ℤ, a * a = 1 ↔ a = 1 ⊎ a = -1 :=
    algebra.mul_self_eq_one_iff
  definition dvd_of_mul_dvd_mul_left : Π{a b c : ℤ}, a ≠ 0 → a*b ∣ a*c → b ∣ c :=
    @algebra.dvd_of_mul_dvd_mul_left _ _
  definition dvd_of_mul_dvd_mul_right : Π{a b c : ℤ}, a ≠ 0 → b*a ∣ c*a → b ∣ c :=
    @algebra.dvd_of_mul_dvd_mul_right _ _
end port_algebra

/- additional properties -/

definition of_nat_sub_of_nat {m n : ℕ} (H : #nat m ≥ n) : of_nat m - of_nat n = of_nat (#nat m - n) :=
have H1 : m = (#nat m - n + n), from (nat.sub_add_cancel H)⁻¹,
have H2 : m = (#nat m - n) + n, from ap of_nat H1,
sub_eq_of_eq_add H2

definition neg_succ_of_nat_eq' (m : ℕ) : -[m +1] = -m - 1 :=
by rewrite [neg_succ_of_nat_eq, -of_nat_add_of_nat, neg_add]

definition succ (a : ℤ) := a + (nat.succ zero)
definition pred (a : ℤ) := a - (nat.succ zero)
definition pred_succ (a : ℤ) : pred (succ a) = a := !sub_add_cancel
definition succ_pred (a : ℤ) : succ (pred a) = a := !add_sub_cancel
definition neg_succ (a : ℤ) : -succ a = pred (-a) :=
by rewrite [↑succ,neg_add]
definition succ_neg_succ (a : ℤ) : succ (-succ a) = -a :=
by rewrite [neg_succ,succ_pred]
definition neg_pred (a : ℤ) : -pred a = succ (-a) :=
by rewrite [↑pred,neg_sub,sub_eq_add_neg,add.comm]
definition pred_neg_pred (a : ℤ) : pred (-pred a) = -a :=
by rewrite [neg_pred,pred_succ]

definition pred_nat_succ (n : ℕ) : pred (nat.succ n) = n := pred_succ n
definition neg_nat_succ (n : ℕ) : -nat.succ n = pred (-n) := !neg_succ
definition succ_neg_nat_succ (n : ℕ) : succ (-nat.succ n) = -n := !succ_neg_succ

definition rec_nat_on [unfold 2] {P : ℤ → Type} (z : ℤ) (H0 : P 0)
  (Hsucc : Π⦃n : ℕ⦄, P n → P (succ n)) (Hpred : Π⦃n : ℕ⦄, P (-n) → P (-nat.succ n)) : P z :=
begin
  induction z with n n,
   {exact nat.rec_on n H0 Hsucc},
   {induction n with m ih,
     exact Hpred H0,
     exact Hpred ih}
end

--the only computation rule of rec_nat_on which is not definitional
definition rec_nat_on_neg {P : ℤ → Type} (n : nat) (H0 : P zero)
  (Hsucc : Π⦃n : nat⦄, P n → P (succ n)) (Hpred : Π⦃n : nat⦄, P (-n) → P (-nat.succ n))
  : rec_nat_on (-nat.succ n) H0 Hsucc Hpred = Hpred (rec_nat_on (-n) H0 Hsucc Hpred) :=
nat.rec_on n rfl (λn H, rfl)

end int
