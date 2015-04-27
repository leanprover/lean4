/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: hit.quotient
Authors: Floris van Doorn

Declaration of set-quotients
-/

import .type_quotient .trunc

open eq is_trunc trunc type_quotient

namespace quotient
section
parameters {A : Type} (R : A → A → hprop)
  -- set-quotients are just truncations of type-quotients
  definition quotient : Type := trunc 0 (type_quotient (λa a', trunctype.carrier (R a a')))

  definition class_of (a : A) : quotient :=
  tr (class_of _ a)

  definition eq_of_rel {a a' : A} (H : R a a') : class_of a = class_of a' :=
  ap tr (eq_of_rel _ H)

  theorem is_hset_quotient : is_hset quotient :=
  begin unfold quotient, exact _ end

  protected definition rec {P : quotient → Type} [Pt : Πaa, is_hset (P aa)]
    (Pc : Π(a : A), P (class_of a)) (Pp : Π⦃a a' : A⦄ (H : R a a'), eq_of_rel H ▹ Pc a = Pc a')
    (x : quotient) : P x :=
  begin
    apply (@trunc.rec_on _ _ P x),
    { intro x', apply Pt},
    { intro y, fapply (type_quotient.rec_on y),
      { exact Pc},
      { intros [a, a', H],
        apply concat, apply transport_compose;apply Pp}}
  end

  protected definition rec_on [reducible] {P : quotient → Type} (x : quotient)
    [Pt : Πaa, is_hset (P aa)] (Pc : Π(a : A), P (class_of a))
    (Pp : Π⦃a a' : A⦄ (H : R a a'), eq_of_rel H ▹ Pc a = Pc a') : P x :=
  rec Pc Pp x

  theorem rec_eq_of_rel {P : quotient → Type} [Pt : Πaa, is_hset (P aa)]
    (Pc : Π(a : A), P (class_of a)) (Pp : Π⦃a a' : A⦄ (H : R a a'), eq_of_rel H ▹ Pc a = Pc a')
    {a a' : A} (H : R a a') : apd (rec Pc Pp) (eq_of_rel H) = Pp H :=
  sorry

  protected definition elim {P : Type} [Pt : is_hset P] (Pc : A → P)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a') (x : quotient) : P :=
  rec Pc (λa a' H, !tr_constant ⬝ Pp H) x

  protected definition elim_on [reducible] {P : Type} (x : quotient) [Pt : is_hset P]
    (Pc : A → P) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a')  : P :=
  elim Pc Pp x

  theorem elim_eq_of_rel {P : Type} [Pt : is_hset P] (Pc : A → P)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a') {a a' : A} (H : R a a')
    : ap (elim Pc Pp) (eq_of_rel H) = Pp H :=
  begin
    apply (@cancel_left _ _ _ _ (tr_constant (eq_of_rel H) (elim Pc Pp (class_of a)))),
    rewrite [-apd_eq_tr_constant_con_ap,↑elim,rec_eq_of_rel],
  end

  /-
    there are no theorems to eliminate to the universe here,
    because the universe is generally not a set
  -/

end
end quotient
