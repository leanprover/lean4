/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: hit.suspension
Authors: Floris van Doorn

Declaration of suspension
-/

import .pushout

open pushout unit eq equiv equiv.ops

definition suspension (A : Type) : Type := pushout (λ(a : A), star.{0}) (λ(a : A), star.{0})

namespace suspension
  variable {A : Type}

  definition north (A : Type) : suspension A :=
  inl _ _ star

  definition south (A : Type) : suspension A :=
  inr _ _ star

  definition merid (a : A) : north A = south A :=
  glue _ _ a

  protected definition rec {P : suspension A → Type} (PN : P !north) (PS : P !south)
    (Pm : Π(a : A), merid a ▹ PN = PS) (x : suspension A) : P x :=
  begin
    fapply (pushout.rec_on _ _ x),
    { intro u, cases u, exact PN},
    { intro u, cases u, exact PS},
    { exact Pm},
  end

  protected definition rec_on [reducible] {P : suspension A → Type} (y : suspension A)
    (PN : P !north) (PS : P !south) (Pm : Π(a : A), merid a ▹ PN = PS) : P y :=
  rec PN PS Pm y

  theorem rec_merid {P : suspension A → Type} (PN : P !north) (PS : P !south)
    (Pm : Π(a : A), merid a ▹ PN = PS) (a : A)
      : apd (rec PN PS Pm) (merid a) = Pm a :=
  !rec_glue

  protected definition elim {P : Type} (PN : P) (PS : P) (Pm : A → PN = PS)
    (x : suspension A) : P :=
  rec PN PS (λa, !tr_constant ⬝ Pm a) x

  protected definition elim_on [reducible] {P : Type} (x : suspension A)
    (PN : P) (PS : P)  (Pm : A → PN = PS) : P :=
  elim PN PS Pm x

  theorem elim_merid {P : Type} (PN : P) (PS : P) (Pm : A → PN = PS) (a : A)
    : ap (elim PN PS Pm) (merid a) = Pm a :=
  begin
    apply (@cancel_left _ _ _ _ (tr_constant (merid a) (elim PN PS Pm !north))),
    rewrite [-apd_eq_tr_constant_con_ap,↑elim,rec_merid],
  end

  protected definition elim_type (PN : Type) (PS : Type) (Pm : A → PN ≃ PS)
    (x : suspension A) : Type :=
  elim PN PS (λa, ua (Pm a)) x

  protected definition elim_type_on [reducible] (x : suspension A)
    (PN : Type) (PS : Type)  (Pm : A → PN ≃ PS) : Type :=
  elim_type PN PS Pm x

  theorem elim_type_merid (PN : Type) (PS : Type) (Pm : A → PN ≃ PS)
    (x : suspension A) (a : A) : transport (elim_type PN PS Pm) (merid a) = Pm a :=
  by rewrite [tr_eq_cast_ap_fn,↑elim_type,elim_merid];apply cast_ua_fn

end suspension
