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
open eq.ops
open prod relation nat
open decidable binary

/- the type of integers -/

inductive int : Type :=
| of_nat : nat → int
| neg_succ_of_nat : nat → int

notation `ℤ` := int
definition int.of_num [coercion] [reducible] [constructor] (n : num) : ℤ :=
int.of_nat (nat.of_num n)

namespace int

attribute int.of_nat [coercion]

notation `-[1+` n `]` := int.neg_succ_of_nat n    -- for pretty-printing output

/- definitions of basic functions -/

definition neg_of_nat : ℕ → ℤ
| 0 := 0
| (succ m) := -[1+ m]

definition sub_nat_nat (m n : ℕ) : ℤ :=
match n - m with
  | 0        := m - n       -- m ≥ n
  | (succ k) := -[1+ k]     -- m < n, and n - m = succ k
end

definition neg (a : ℤ) : ℤ :=
int.cases_on a neg_of_nat succ

definition add : ℤ → ℤ → ℤ
| (of_nat m) (of_nat n) := m + n
| (of_nat m) -[1+ n]    := sub_nat_nat m (succ n)
| -[1+ m]    (of_nat n) := sub_nat_nat n (succ m)
| -[1+ m]    -[1+ n]    := neg_of_nat (succ m + succ n)

definition mul : ℤ → ℤ → ℤ
| (of_nat m) (of_nat n) := m * n
| (of_nat m) -[1+ n]    := neg_of_nat (m * succ n)
| -[1+ m]    (of_nat n) := neg_of_nat (succ m * n)
| -[1+ m]    -[1+ n]    := succ m * succ n

/- notation -/

protected definition prio : num := num.pred std.priority.default

prefix [priority int.prio] - := int.neg
infix  [priority int.prio] +  := int.add
infix  [priority int.prio] *  := int.mul

/- some basic functions and properties -/

theorem of_nat.inj {m n : ℕ} (H : of_nat m = of_nat n) : m = n :=
int.no_confusion H imp.id

theorem of_nat_eq_of_nat (m n : ℕ) : of_nat m = of_nat n ↔ m = n :=
iff.intro of_nat.inj !congr_arg

theorem neg_succ_of_nat.inj {m n : ℕ} (H : neg_succ_of_nat m = neg_succ_of_nat n) : m = n :=
int.no_confusion H imp.id

theorem neg_succ_of_nat_eq (n : ℕ) : -[1+ n] = -(n + 1) := rfl

private definition has_decidable_eq₂ : Π (a b : ℤ), decidable (a = b)
| (of_nat m) (of_nat n) := decidable_of_decidable_of_iff
    (nat.has_decidable_eq m n) (iff.symm (of_nat_eq_of_nat m n))
| (of_nat m) -[1+ n]    := inr (by contradiction)
| -[1+ m]    (of_nat n) := inr (by contradiction)
| -[1+ m]    -[1+ n]    := if H : m = n then
    inl (congr_arg neg_succ_of_nat H) else inr (not.mto neg_succ_of_nat.inj H)

definition has_decidable_eq [instance] : decidable_eq ℤ := has_decidable_eq₂

theorem of_nat_add (n m : nat) : of_nat (n + m) = of_nat n + of_nat m := rfl

theorem of_nat_succ (n : ℕ) : of_nat (succ n) = of_nat n + 1 := rfl

theorem of_nat_mul (n m : ℕ) : of_nat (n * m) = of_nat n * of_nat m := rfl

theorem sub_nat_nat_of_ge {m n : ℕ} (H : m ≥ n) : sub_nat_nat m n = of_nat (m - n) :=
show sub_nat_nat m n = nat.cases_on 0 (m - n) _, from (sub_eq_zero_of_le H) ▸ rfl

section
local attribute sub_nat_nat [reducible]
theorem sub_nat_nat_of_lt {m n : ℕ} (H : m < n) :
  sub_nat_nat m n = -[1+ pred (n - m)] :=
have H1 : n - m = succ (pred (n - m)), from (succ_pred_of_pos (sub_pos_of_lt H))⁻¹,
show sub_nat_nat m n = nat.cases_on (succ (pred (n - m))) (m - n) _, from H1 ▸ rfl
end

definition nat_abs (a : ℤ) : ℕ := int.cases_on a function.id succ

theorem nat_abs_of_nat (n : ℕ) : nat_abs n = n := rfl

theorem nat_abs_eq_zero : Π {a : ℤ}, nat_abs a = 0 → a = 0
| (of_nat m) H := congr_arg of_nat H
| -[1+ m']   H := absurd H !succ_ne_zero

/- int is a quotient of ordered pairs of natural numbers -/

protected definition equiv (p q : ℕ × ℕ) : Prop :=  pr1 p + pr2 q = pr2 p + pr1 q

local infix `≡` := int.equiv

protected theorem equiv.refl [refl] {p : ℕ × ℕ} : p ≡ p := !add.comm

protected theorem equiv.symm [symm] {p q : ℕ × ℕ} (H : p ≡ q) : q ≡ p :=
calc
  pr1 q + pr2 p = pr2 p + pr1 q : add.comm
    ... = pr1 p + pr2 q         : H⁻¹
    ... = pr2 q + pr1 p         : add.comm

protected theorem equiv.trans [trans] {p q r : ℕ × ℕ} (H1 : p ≡ q) (H2 : q ≡ r) : p ≡ r :=
add.cancel_right (calc
   pr1 p + pr2 r + pr2 q = pr1 p + pr2 q + pr2 r : add.right_comm
    ... = pr2 p + pr1 q + pr2 r                  : {H1}
    ... = pr2 p + (pr1 q + pr2 r)                : add.assoc
    ... = pr2 p + (pr2 q + pr1 r)                : {H2}
    ... = pr2 p + pr2 q + pr1 r                  : add.assoc
    ... = pr2 p + pr1 r + pr2 q                  : add.right_comm)

protected theorem equiv_equiv : is_equivalence int.equiv :=
is_equivalence.mk @equiv.refl @equiv.symm @equiv.trans

protected theorem equiv_cases {p q : ℕ × ℕ} (H : p ≡ q) :
    (pr1 p ≥ pr2 p ∧ pr1 q ≥ pr2 q) ∨ (pr1 p < pr2 p ∧ pr1 q < pr2 q) :=
or.elim (@le_or_gt (pr2 p) (pr1 p))
  (suppose pr1 p ≥ pr2 p,
    have pr2 p + pr1 q ≥ pr2 p + pr2 q, from H ▸ add_le_add_right this (pr2 q),
    or.inl (and.intro `pr1 p ≥ pr2 p` (le_of_add_le_add_left this)))
  (suppose pr1 p < pr2 p,
    have pr2 p + pr1 q < pr2 p + pr2 q, from H ▸ add_lt_add_right this (pr2 q),
    or.inr (and.intro `pr1 p < pr2 p` (lt_of_add_lt_add_left this)))

protected theorem equiv_of_eq {p q : ℕ × ℕ} (H : p = q) : p ≡ q := H ▸ equiv.refl

/- the representation and abstraction functions -/

definition abstr (a : ℕ × ℕ) : ℤ := sub_nat_nat (pr1 a) (pr2 a)

theorem abstr_of_ge {p : ℕ × ℕ} (H : pr1 p ≥ pr2 p) : abstr p = of_nat (pr1 p - pr2 p) :=
sub_nat_nat_of_ge H

theorem abstr_of_lt {p : ℕ × ℕ} (H : pr1 p < pr2 p) :
  abstr p = -[1+ pred (pr2 p - pr1 p)] :=
sub_nat_nat_of_lt H

definition repr : ℤ → ℕ × ℕ
| (of_nat m) := (m, 0)
| -[1+ m]    := (0, succ m)

theorem abstr_repr : Π (a : ℤ), abstr (repr a) = a
| (of_nat m) := (sub_nat_nat_of_ge (zero_le m))
| -[1+ m]    := rfl

theorem repr_sub_nat_nat (m n : ℕ) : repr (sub_nat_nat m n) ≡ (m, n) :=
lt_ge_by_cases
  (take H : m < n,
    have H1 : repr (sub_nat_nat m n) = (0, n - m), by
      rewrite [sub_nat_nat_of_lt H, -(succ_pred_of_pos (sub_pos_of_lt H))],
    H1⁻¹ ▸ (!zero_add ⬝ (sub_add_cancel (le_of_lt H))⁻¹))
  (take H : m ≥ n,
    have H1 : repr (sub_nat_nat m n) = (m - n, 0), from sub_nat_nat_of_ge H ▸ rfl,
    H1⁻¹ ▸ ((sub_add_cancel H) ⬝ !zero_add⁻¹))

theorem repr_abstr (p : ℕ × ℕ) : repr (abstr p) ≡ p :=
!prod.eta ▸ !repr_sub_nat_nat

theorem abstr_eq {p q : ℕ × ℕ} (Hequiv : p ≡ q) : abstr p = abstr q :=
or.elim (int.equiv_cases Hequiv)
  (and.rec (assume (Hp : pr1 p ≥ pr2 p) (Hq : pr1 q ≥ pr2 q),
    have H : pr1 p - pr2 p = pr1 q - pr2 q, from
      calc pr1 p - pr2 p
           = pr1 p + pr2 q - pr2 q - pr2 p   : add_sub_cancel
       ... = pr2 p + pr1 q - pr2 q - pr2 p   : Hequiv
       ... = pr2 p + (pr1 q - pr2 q) - pr2 p : add_sub_assoc Hq
       ... = pr1 q - pr2 q + pr2 p - pr2 p   : add.comm
       ... = pr1 q - pr2 q                   : add_sub_cancel,
    abstr_of_ge Hp ⬝ (H ▸ rfl) ⬝ (abstr_of_ge Hq)⁻¹))
  (and.rec (assume (Hp : pr1 p < pr2 p) (Hq : pr1 q < pr2 q),
    have H : pr2 p - pr1 p = pr2 q - pr1 q, from
      calc pr2 p - pr1 p
           = pr2 p + pr1 q - pr1 q - pr1 p   : add_sub_cancel
       ... = pr1 p + pr2 q - pr1 q - pr1 p   : Hequiv
       ... = pr1 p + (pr2 q - pr1 q) - pr1 p : add_sub_assoc (le_of_lt Hq)
       ... = pr2 q - pr1 q + pr1 p - pr1 p   : add.comm
       ... = pr2 q - pr1 q                   : add_sub_cancel,
    abstr_of_lt Hp ⬝ (H ▸ rfl) ⬝ (abstr_of_lt Hq)⁻¹))

theorem equiv_iff (p q : ℕ × ℕ) : (p ≡ q) ↔ (abstr p = abstr q) :=
iff.intro abstr_eq (assume H, equiv.trans (H ▸ equiv.symm (repr_abstr p)) (repr_abstr q))

theorem equiv_iff3 (p q : ℕ × ℕ) : (p ≡ q) ↔ ((p ≡ p) ∧ (q ≡ q) ∧ (abstr p = abstr q)) :=
iff.trans !equiv_iff (iff.symm
   (iff.trans (and_iff_right !equiv.refl) (and_iff_right !equiv.refl)))

theorem eq_abstr_of_equiv_repr {a : ℤ} {p : ℕ × ℕ} (Hequiv : repr a ≡ p) : a = abstr p :=
!abstr_repr⁻¹ ⬝ abstr_eq Hequiv

theorem eq_of_repr_equiv_repr {a b : ℤ} (H : repr a ≡ repr b) : a = b :=
eq_abstr_of_equiv_repr H ⬝ !abstr_repr

section
local attribute abstr [reducible]
local attribute dist [reducible]
theorem nat_abs_abstr : Π (p : ℕ × ℕ), nat_abs (abstr p) = dist (pr1 p) (pr2 p)
| (m, n) := lt_ge_by_cases
  (assume H : m < n,
    calc
      nat_abs (abstr (m, n)) = nat_abs (-[1+ pred (n - m)]) : int.abstr_of_lt H
        ... = n - m               : succ_pred_of_pos (sub_pos_of_lt H)
        ... = dist m n            : dist_eq_sub_of_le (le_of_lt H))
  (assume H : m ≥ n, (abstr_of_ge H)⁻¹ ▸ (dist_eq_sub_of_ge H)⁻¹)
end

theorem cases_of_nat_succ (a : ℤ) : (∃n : ℕ, a = of_nat n) ∨ (∃n : ℕ, a = - (of_nat (succ n))) :=
int.cases_on a (take m, or.inl (exists.intro _ rfl)) (take m, or.inr (exists.intro _ rfl))

theorem cases_of_nat (a : ℤ) : (∃n : ℕ, a = of_nat n) ∨ (∃n : ℕ, a = - of_nat n) :=
or.imp_right (Exists.rec (take n, (exists.intro _))) !cases_of_nat_succ

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

theorem repr_add : Π (a b : ℤ), repr (add a b) ≡ padd (repr a) (repr b)
| (of_nat m) (of_nat n) := !equiv.refl
| (of_nat m) -[1+ n]    := (!zero_add ▸ rfl)⁻¹ ▸ !repr_sub_nat_nat
| -[1+ m]    (of_nat n) := (!zero_add ▸ rfl)⁻¹ ▸ !repr_sub_nat_nat
| -[1+ m]    -[1+ n]    := !repr_sub_nat_nat

theorem padd_congr {p p' q q' : ℕ × ℕ} (Ha : p ≡ p') (Hb : q ≡ q') : padd p q ≡ padd p' q' :=
calc pr1 p + pr1 q + (pr2 p' + pr2 q')
        = pr1 p + pr2 p' + (pr1 q + pr2 q') : add.comm4
    ... = pr2 p + pr1 p' + (pr1 q + pr2 q') : {Ha}
    ... = pr2 p + pr1 p' + (pr2 q + pr1 q') : {Hb}
    ... = pr2 p + pr2 q + (pr1 p' + pr1 q') : add.comm4

theorem padd_comm (p q : ℕ × ℕ) : padd p q = padd q p :=
calc (pr1 p + pr1 q, pr2 p + pr2 q)
        = (pr1 q + pr1 p, pr2 p + pr2 q) : add.comm
    ... = (pr1 q + pr1 p, pr2 q + pr2 p) : add.comm

theorem padd_assoc (p q r : ℕ × ℕ) : padd (padd p q) r = padd p (padd q r) :=
calc (pr1 p + pr1 q + pr1 r, pr2 p + pr2 q + pr2 r)
        = (pr1 p + (pr1 q + pr1 r), pr2 p + pr2 q + pr2 r) : add.assoc
    ... = (pr1 p + (pr1 q + pr1 r), pr2 p + (pr2 q + pr2 r)) : add.assoc

theorem add.comm (a b : ℤ) : a + b = b + a :=
eq_of_repr_equiv_repr (equiv.trans !repr_add
   (equiv.symm (!padd_comm ▸ !repr_add)))

theorem add.assoc (a b c : ℤ) : a + b + c = a + (b + c) :=
eq_of_repr_equiv_repr (calc
         repr (a + b + c)
       ≡ padd (repr (a + b)) (repr c)           : repr_add
  ...  ≡ padd (padd (repr a) (repr b)) (repr c) : padd_congr !repr_add !equiv.refl
  ...  = padd (repr a) (padd (repr b) (repr c)) : !padd_assoc
  ...  ≡ padd (repr a) (repr (b + c))           : padd_congr !equiv.refl !repr_add
  ...  ≡ repr (a + (b + c))                     : repr_add)

theorem add_zero : Π (a : ℤ), a + 0 = a := int.rec (λm, rfl) (λm, rfl)

theorem zero_add (a : ℤ) : 0 + a = a := !add.comm ▸ !add_zero

/- negation -/

definition pneg (p : ℕ × ℕ) : ℕ × ℕ := (pr2 p, pr1 p)

-- note: this is =, not just ≡
theorem repr_neg : Π (a : ℤ), repr (- a) = pneg (repr a)
| 0        := rfl
| (succ m) := rfl
| -[1+ m]  := rfl

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
calc      pr1 p + pr1 q + pr2 q + pr2 p
        = pr1 p + (pr1 q + pr2 q) + pr2 p : nat.add.assoc
    ... = pr1 p + (pr1 q + pr2 q + pr2 p) : nat.add.assoc
    ... = pr1 p + (pr2 q + pr1 q + pr2 p) : nat.add.comm
    ... = pr1 p + (pr2 q + pr2 p + pr1 q) : add.right_comm
    ... = pr1 p + (pr2 p + pr2 q + pr1 q) : nat.add.comm
    ... = pr2 p + pr2 q + pr1 q + pr1 p   : nat.add.comm

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
calc
  nat_abs (a + b) = pabs (repr (a + b)) : nat_abs_eq_pabs_repr 
              ... = pabs (padd (repr a) (repr b)) : pabs_congr !repr_add
              ... ≤ pabs (repr a) + pabs (repr b) : dist_add_add_le_add_dist_dist
              ... = pabs (repr a) + nat_abs b     : nat_abs_eq_pabs_repr
              ... = nat_abs a + nat_abs b         : nat_abs_eq_pabs_repr

section
local attribute nat_abs [reducible]
theorem nat_abs_mul : Π (a b : ℤ), nat_abs (a * b) = (nat_abs a) * (nat_abs b)
| (of_nat m) (of_nat n) := rfl
| (of_nat m) -[1+ n]    := !nat_abs_neg ▸ rfl
| -[1+ m]    (of_nat n) := !nat_abs_neg ▸ rfl
| -[1+ m]    -[1+ n]    := rfl
end

/- multiplication -/

definition pmul (p q : ℕ × ℕ) : ℕ × ℕ :=
  (pr1 p * pr1 q + pr2 p * pr2 q, pr1 p * pr2 q + pr2 p * pr1 q)

theorem repr_neg_of_nat (m : ℕ) : repr (neg_of_nat m) = (0, m) :=
nat.cases_on m rfl (take m', rfl)

-- note: we have =, not just ≡
theorem repr_mul : Π (a b : ℤ), repr (a * b) = pmul (repr a) (repr b)
| (of_nat m) (of_nat n) := calc
          (m * n + 0 * 0, m * 0 + 0) = (m * n + 0 * 0, m * 0 + 0 * n) : zero_mul
| (of_nat m) -[1+ n]    := calc
          repr (m * -[1+ n]) = (m * 0 + 0, m * succ n + 0 * 0) : repr_neg_of_nat
            ... = (m * 0 + 0 * succ n, m * succ n + 0 * 0) : zero_mul
| -[1+ m]    (of_nat n) := calc
          repr (-[1+ m] * n) = (0 + succ m * 0, succ m * n) : repr_neg_of_nat
            ... = (0 + succ m * 0, 0 + succ m * n) : nat.zero_add
            ... = (0 * n + succ m * 0, 0 + succ m * n) : zero_mul
| -[1+ m]    -[1+ n]    := calc
          (succ m * succ n, 0) = (succ m * succ n, 0 * succ n) : zero_mul
            ... = (0 + succ m * succ n, 0 * succ n) : nat.zero_add

theorem equiv_mul_prep {xa ya xb yb xn yn xm ym : ℕ}
  (H1 : xa + yb = ya + xb) (H2 : xn + ym = yn + xm)
: xa*xn+ya*yn+(xb*ym+yb*xm) = xa*yn+ya*xn+(xb*xm+yb*ym) :=
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

theorem pmul_congr {p p' q q' : ℕ × ℕ} : p ≡ p' → q ≡ q' → pmul p q ≡ pmul p' q' := equiv_mul_prep

theorem pmul_comm (p q : ℕ × ℕ) : pmul p q = pmul q p :=
show (_,_) = (_,_), from !congr_arg2
   (!congr_arg2 !mul.comm !mul.comm) (!nat.add.comm ⬝ (!congr_arg2 !mul.comm !mul.comm))

theorem mul.comm (a b : ℤ) : a * b = b * a :=
eq_of_repr_equiv_repr
  ((calc
    repr (a * b) = pmul (repr a) (repr b) : repr_mul
      ... = pmul (repr b) (repr a) : pmul_comm
      ... = repr (b * a) : repr_mul) ▸ !equiv.refl)

private theorem pmul_assoc_prep {p1 p2 q1 q2 r1 r2 : ℕ} :
  ((p1*q1+p2*q2)*r1+(p1*q2+p2*q1)*r2, (p1*q1+p2*q2)*r2+(p1*q2+p2*q1)*r1) =
   (p1*(q1*r1+q2*r2)+p2*(q1*r2+q2*r1), p1*(q1*r2+q2*r1)+p2*(q1*r1+q2*r2)) :=
by rewrite[+mul.left_distrib,+mul.right_distrib,*mul.assoc];
   exact (congr_arg2 pair (!add.comm4 ⬝ (!congr_arg !nat.add.comm))
                          (!add.comm4 ⬝ (!congr_arg !nat.add.comm)))

theorem pmul_assoc (p q r: ℕ × ℕ) : pmul (pmul p q) r = pmul p (pmul q r) := pmul_assoc_prep

theorem mul.assoc (a b c : ℤ) : (a * b) * c = a * (b * c) :=
eq_of_repr_equiv_repr
  ((calc
    repr (a * b * c) = pmul (repr (a * b)) (repr c) : repr_mul
      ... = pmul (pmul (repr a) (repr b)) (repr c) : repr_mul
      ... = pmul (repr a) (pmul (repr b) (repr c)) : pmul_assoc
      ... = pmul (repr a) (repr (b * c)) : repr_mul
      ... = repr (a * (b * c)) : repr_mul) ▸ !equiv.refl)

theorem mul_one : Π (a : ℤ), a * 1 = a
| (of_nat m) := !zero_add -- zero_add happens to be def. = to this thm
| -[1+ m]    := !nat.zero_add ▸ rfl


theorem one_mul (a : ℤ) : 1 * a = a :=
mul.comm a 1 ▸ mul_one a

private theorem mul_distrib_prep {a1 a2 b1 b2 c1 c2 : ℕ} :
 ((a1+b1)*c1+(a2+b2)*c2, (a1+b1)*c2+(a2+b2)*c1) = 
 (a1*c1+a2*c2+(b1*c1+b2*c2), a1*c2+a2*c1+(b1*c2+b2*c1)) :=
by rewrite[+mul.right_distrib] ⬝ (!congr_arg2 !add.comm4 !add.comm4)

theorem mul.right_distrib (a b c : ℤ) : (a + b) * c = a * c + b * c :=
eq_of_repr_equiv_repr
  (calc
    repr ((a + b) * c) = pmul (repr (a + b)) (repr c) : repr_mul
      ... ≡ pmul (padd (repr a) (repr b)) (repr c) : pmul_congr !repr_add equiv.refl
      ... = padd (pmul (repr a) (repr c)) (pmul (repr b) (repr c)) : mul_distrib_prep
      ... = padd (repr (a * c)) (pmul (repr b) (repr c)) : repr_mul
      ... = padd (repr (a * c)) (repr (b * c)) : repr_mul
      ... ≡ repr (a * c + b * c) : repr_add)

theorem mul.left_distrib (a b c : ℤ) : a * (b + c) = a * b + a * c :=
calc
  a * (b + c) = (b + c) * a : mul.comm
    ... = b * a + c * a : mul.right_distrib
    ... = a * b + c * a : mul.comm
    ... = a * b + a * c : mul.comm

theorem zero_ne_one : (0 : int) ≠ 1 :=
assume H : 0 = 1, !succ_ne_zero (of_nat.inj H)⁻¹

theorem eq_zero_or_eq_zero_of_mul_eq_zero {a b : ℤ} (H : a * b = 0) : a = 0 ∨ b = 0 :=
or.imp nat_abs_eq_zero nat_abs_eq_zero (eq_zero_or_eq_zero_of_mul_eq_zero (H ▸ (nat_abs_mul a b)⁻¹))

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
    one            := 1,
    one_mul        := one_mul,
    mul_one        := mul_one,
    left_distrib   := mul.left_distrib,
    right_distrib  := mul.right_distrib,
    mul_comm       := mul.comm,
    eq_zero_or_eq_zero_of_mul_eq_zero := @eq_zero_or_eq_zero_of_mul_eq_zero⦄

  local attribute int.integral_domain [instance]
  definition sub (a b : ℤ) : ℤ := algebra.sub a b
  infix [priority int.prio] - := int.sub
  definition dvd (a b : ℤ) : Prop := algebra.dvd a b
  notation [priority int.prio] a ∣ b := dvd a b

  migrate from algebra with int
  replacing sub → sub, dvd → dvd
end migrate_algebra

/- additional properties -/
theorem of_nat_sub {m n : ℕ} (H : m ≥ n) : m - n = sub m n :=
(sub_eq_of_eq_add (!congr_arg (nat.sub_add_cancel H)⁻¹))⁻¹

theorem neg_succ_of_nat_eq' (m : ℕ) : -[1+ m] = -m - 1 :=
by rewrite [neg_succ_of_nat_eq, of_nat_add, neg_add]

definition succ (a : ℤ) := a + (succ zero)
definition pred (a : ℤ) := a - (succ zero)
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

definition rec_nat_on [unfold 2] {P : ℤ → Type} (z : ℤ) (H0 : P 0)
  (Hsucc : Π⦃n : ℕ⦄, P n → P (succ n)) (Hpred : Π⦃n : ℕ⦄, P (-n) → P (-nat.succ n)) : P z :=
int.rec (nat.rec H0 Hsucc) (λn, nat.rec H0 Hpred (nat.succ n)) z

--the only computation rule of rec_nat_on which is not definitional
theorem rec_nat_on_neg {P : ℤ → Type} (n : nat) (H0 : P zero)
  (Hsucc : Π⦃n : nat⦄, P n → P (succ n)) (Hpred : Π⦃n : nat⦄, P (-n) → P (-nat.succ n))
  : rec_nat_on (-nat.succ n) H0 Hsucc Hpred = Hpred (rec_nat_on (-n) H0 Hsucc Hpred) :=
nat.rec rfl (λn H, rfl) n

end int
