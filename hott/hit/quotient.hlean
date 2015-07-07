/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Quotients. This is a quotient without truncation for an arbitrary type-valued binary relation.
See also .set_quotient
-/

/-
  The hit quotient is primitive, declared in init.hit.
  The constructors are, given {A : Type} (R : A → A → Type),
  * class_of : A → quotient R (A implicit, R explicit)
  * eq_of_rel : Π{a a' : A}, R a a' → class_of a = class_of a' (R explicit)
-/

open eq equiv sigma.ops

namespace quotient

  variables {A : Type} {R : A → A → Type}

  protected definition elim {P : Type} (Pc : A → P) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a')
    (x : quotient R) : P :=
  quotient.rec Pc (λa a' H, pathover_of_eq (Pp H)) x

  protected definition elim_on [reducible] {P : Type} (x : quotient R)
    (Pc : A → P) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a') : P :=
  quotient.elim Pc Pp x

  theorem elim_eq_of_rel {P : Type} (Pc : A → P)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a') {a a' : A} (H : R a a')
    : ap (quotient.elim Pc Pp) (eq_of_rel R H) = Pp H :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant (eq_of_rel R H)),
    rewrite [▸*,-apdo_eq_pathover_of_eq_ap,↑quotient.elim,rec_eq_of_rel],
  end

  protected definition elim_type (Pc : A → Type)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a') : quotient R → Type :=
  quotient.elim Pc (λa a' H, ua (Pp H))

  protected definition elim_type_on [reducible] (x : quotient R) (Pc : A → Type)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a') : Type :=
  quotient.elim_type Pc Pp x

  theorem elim_type_eq_of_rel (Pc : A → Type)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a') {a a' : A} (H : R a a')
    : transport (quotient.elim_type Pc Pp) (eq_of_rel R H) = to_fun (Pp H) :=
  by rewrite [tr_eq_cast_ap_fn, ↑quotient.elim_type, elim_eq_of_rel];apply cast_ua_fn

  definition elim_type_uncurried (H : Σ(Pc : A → Type),  Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a')
    : quotient R → Type :=
  quotient.elim_type H.1 H.2
end quotient

attribute quotient.rec [recursor]
attribute quotient.elim [unfold 6] [recursor 6]
attribute quotient.elim_type [unfold 5]
attribute quotient.elim_on [unfold 4]
attribute quotient.elim_type_on [unfold 3]
