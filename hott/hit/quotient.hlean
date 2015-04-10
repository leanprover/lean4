/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: hit.quotient
Authors: Floris van Doorn

Declaration of set-quotients
-/

/-
We aim to model
HIT quotient : Type :=
   | class_of : A -> quotient
   | eq_of_rel : Πa a', R a a' → class_of a = class_of a'
   | is_hset_quotient : is_hset quotient
-/

import .coeq .trunc

open coeq eq is_trunc trunc

namespace quotient
context
universe u
parameters {A : Type.{u}} (R : A → A → hprop.{u})

  structure total : Type := {pt1 : A} {pt2 : A} (rel : R pt1 pt2)
  open total

  definition quotient : Type :=
  trunc 0 (coeq (pt1 : total → A) (pt2 : total → A))

  definition class_of (a : A) : quotient :=
  tr (coeq_i _ _ a)

  definition eq_of_rel {a a' : A} (H : R a a') : class_of a = class_of a' :=
  ap tr (cp _ _ (total.mk H))

  definition is_hset_quotient : is_hset quotient :=
  by unfold quotient; exact _

  protected definition rec {P : quotient → Type} [Pt : Πaa, is_trunc 0 (P aa)]
    (Pc : Π(a : A), P (class_of a)) (Pp : Π⦃a a' : A⦄ (H : R a a'), eq_of_rel H ▹ Pc a = Pc a')
    (x : quotient) : P x :=
  begin
    apply (@trunc.rec_on _ _ P x),
    { intro x', apply Pt},
    { intro y, fapply (coeq.rec_on _ _ y),
      { exact Pc},
      { intro H, cases H with [a, a', H], esimp [is_typeof],
        --rewrite (transport_compose P tr (cp pt1 pt2 (total.mk H)) (Pc a))
        apply concat, apply transport_compose;apply Pp}}
  end

  protected definition rec_on [reducible] {P : quotient → Type} (x : quotient)
    [Pt : Πaa, is_trunc 0 (P aa)] (Pc : Π(a : A), P (class_of a))
    (Pp : Π⦃a a' : A⦄ (H : R a a'), eq_of_rel H ▹ Pc a = Pc a') : P x :=
  rec Pc Pp x

  definition rec_eq_of_rel {P : quotient → Type} [Pt : Πaa, is_trunc 0 (P aa)]
    (Pc : Π(a : A), P (class_of a)) (Pp : Π⦃a a' : A⦄ (H : R a a'), eq_of_rel H ▹ Pc a = Pc a')
    {a a' : A} (H : R a a') : apD (rec Pc Pp) (eq_of_rel H) = sorry ⬝ Pp H ⬝ sorry :=
  sorry

  protected definition elim {P : Type} [Pt : is_trunc 0 P] (Pc : A → P)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a') (x : quotient) : P :=
  rec Pc (λa a' H, !tr_constant ⬝ Pp H) x

  protected definition elim_on [reducible] {P : Type} (x : quotient) [Pt : is_trunc 0 P]
    (Pc : A → P) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a')  : P :=
  elim Pc Pp x

  protected definition elim_eq_of_rel {P : Type} [Pt : is_trunc 0 P] (Pc : A → P)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a') {a a' : A} (H : R a a')
    : ap (elim Pc Pp) (eq_of_rel H) = sorry ⬝ Pp H ⬝ sorry :=
  sorry

end
end quotient
