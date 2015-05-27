/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Declaration of set-quotients
-/

import .type_quotient .trunc

open eq is_trunc trunc type_quotient equiv

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
    (Pc : Π(a : A), P (class_of a)) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[eq_of_rel H] Pc a')
    (x : quotient) : P x :=
  begin
    apply (@trunc.rec_on _ _ P x),
    { intro x', apply Pt},
    { intro y, fapply (type_quotient.rec_on y),
      { exact Pc},
      { intros, apply equiv.to_inv !(pathover_compose _ tr), apply Pp}}
  end

  protected definition rec_on [reducible] {P : quotient → Type} (x : quotient)
    [Pt : Πaa, is_hset (P aa)] (Pc : Π(a : A), P (class_of a))
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[eq_of_rel H] Pc a') : P x :=
  rec Pc Pp x

  theorem rec_eq_of_rel {P : quotient → Type} [Pt : Πaa, is_hset (P aa)]
    (Pc : Π(a : A), P (class_of a)) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[eq_of_rel H] Pc a')
    {a a' : A} (H : R a a') : apdo (rec Pc Pp) (eq_of_rel H) = Pp H :=
  !is_hset.elimo

  protected definition elim {P : Type} [Pt : is_hset P] (Pc : A → P)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a') (x : quotient) : P :=
  rec Pc (λa a' H, pathover_of_eq (Pp H)) x

  protected definition elim_on [reducible] {P : Type} (x : quotient) [Pt : is_hset P]
    (Pc : A → P) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a')  : P :=
  elim Pc Pp x

  theorem elim_eq_of_rel {P : Type} [Pt : is_hset P] (Pc : A → P)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a') {a a' : A} (H : R a a')
    : ap (elim Pc Pp) (eq_of_rel H) = Pp H :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant (eq_of_rel H)),
    rewrite [▸*,-apdo_eq_pathover_of_eq_ap,↑elim,rec_eq_of_rel],
  end

  /-
    there are no theorems to eliminate to the universe here,
    because the universe is generally not a set
  -/

end
end quotient

attribute quotient.class_of [constructor]
attribute quotient.rec quotient.elim [unfold-c 7] [recursor 7]
attribute quotient.rec_on quotient.elim_on [unfold-c 4]
