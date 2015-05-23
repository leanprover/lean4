/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Type quotients (quotient without truncation)
-/

/- The hit type_quotient is primitive, declared in init.hit. -/

open eq equiv sigma.ops

namespace type_quotient

  variables {A : Type} {R : A → A → Type}

  protected definition elim {P : Type} (Pc : A → P) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a')
    (x : type_quotient R) : P :=
  type_quotient.rec Pc (λa a' H, !tr_constant ⬝ Pp H) x

  protected definition elim_on [reducible] {P : Type} (x : type_quotient R)
    (Pc : A → P) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a') : P :=
  type_quotient.elim Pc Pp x

  theorem elim_eq_of_rel {P : Type} (Pc : A → P)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a') {a a' : A} (H : R a a')
    : ap (type_quotient.elim Pc Pp) (eq_of_rel R H) = Pp H :=
  begin
    apply (@cancel_left _ _ _ _ (tr_constant (eq_of_rel R H) (type_quotient.elim Pc Pp (class_of R a)))),
    rewrite [-apd_eq_tr_constant_con_ap,↑type_quotient.elim,rec_eq_of_rel],
  end

  protected definition elim_type (Pc : A → Type)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a') : type_quotient R → Type :=
  type_quotient.elim Pc (λa a' H, ua (Pp H))

  protected definition elim_type_on [reducible] (x : type_quotient R) (Pc : A → Type)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a') : Type :=
  type_quotient.elim_type Pc Pp x

  theorem elim_type_eq_of_rel (Pc : A → Type)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a') {a a' : A} (H : R a a')
    : transport (type_quotient.elim_type Pc Pp) (eq_of_rel R H) = to_fun (Pp H) :=
  by rewrite [tr_eq_cast_ap_fn, ↑type_quotient.elim_type, elim_eq_of_rel];apply cast_ua_fn

  definition elim_type_uncurried (H : Σ(Pc : A → Type),  Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a')
    : type_quotient R → Type :=
  type_quotient.elim_type H.1 H.2
end type_quotient

attribute type_quotient.elim [unfold-c 6]
attribute type_quotient.elim_type [unfold-c 5]
attribute type_quotient.elim_on [unfold-c 4]
attribute type_quotient.elim_type_on [unfold-c 3]
