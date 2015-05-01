/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: hit.pushout
Authors: Floris van Doorn

Declaration of the pushout
-/

import .type_quotient

open type_quotient eq sum equiv equiv.ops

namespace pushout
section

parameters {TL BL TR : Type} (f : TL → BL) (g : TL → TR)

  local abbreviation A := BL + TR
  inductive pushout_rel : A → A → Type :=
  | Rmk : Π(x : TL), pushout_rel (inl (f x)) (inr (g x))
  open pushout_rel
  local abbreviation R := pushout_rel

  definition pushout : Type := type_quotient pushout_rel -- TODO: define this in root namespace

  definition inl (x : BL) : pushout :=
  class_of R (inl x)

  definition inr (x : TR) : pushout :=
  class_of R (inr x)

  definition glue (x : TL) : inl (f x) = inr (g x) :=
  eq_of_rel pushout_rel (Rmk f g x)

  protected definition rec {P : pushout → Type} (Pinl : Π(x : BL), P (inl x))
    (Pinr : Π(x : TR), P (inr x)) (Pglue : Π(x : TL), glue x ▸ Pinl (f x) = Pinr (g x))
      (y : pushout) : P y :=
  begin
    fapply (type_quotient.rec_on y),
    { intro a, cases a,
       apply Pinl,
       apply Pinr},
    { intro a a' H, cases H, apply Pglue}
  end

  protected definition rec_on [reducible] {P : pushout → Type} (y : pushout)
    (Pinl : Π(x : BL), P (inl x)) (Pinr : Π(x : TR), P (inr x))
    (Pglue : Π(x : TL), glue x ▸ Pinl (f x) = Pinr (g x)) : P y :=
  rec Pinl Pinr Pglue y

  theorem rec_glue {P : pushout → Type} (Pinl : Π(x : BL), P (inl x))
    (Pinr : Π(x : TR), P (inr x)) (Pglue : Π(x : TL), glue x ▸ Pinl (f x) = Pinr (g x))
      (x : TL) : apd (rec Pinl Pinr Pglue) (glue x) = Pglue x :=
  !rec_eq_of_rel

  protected definition elim {P : Type} (Pinl : BL → P) (Pinr : TR → P)
    (Pglue : Π(x : TL), Pinl (f x) = Pinr (g x)) (y : pushout) : P :=
  rec Pinl Pinr (λx, !tr_constant ⬝ Pglue x) y

  protected definition elim_on [reducible] {P : Type} (y : pushout) (Pinl : BL → P)
    (Pinr : TR → P) (Pglue : Π(x : TL), Pinl (f x) = Pinr (g x)) : P :=
  elim Pinl Pinr Pglue y

  theorem elim_glue {P : Type} (Pinl : BL → P) (Pinr : TR → P)
    (Pglue : Π(x : TL), Pinl (f x) = Pinr (g x)) (x : TL)
    : ap (elim Pinl Pinr Pglue) (glue x) = Pglue x :=
  begin
    apply (@cancel_left _ _ _ _ (tr_constant (glue x) (elim Pinl Pinr Pglue (inl (f x))))),
    rewrite [-apd_eq_tr_constant_con_ap,↑elim,rec_glue],
  end

  protected definition elim_type (Pinl : BL → Type) (Pinr : TR → Type)
    (Pglue : Π(x : TL), Pinl (f x) ≃ Pinr (g x)) (y : pushout) : Type :=
  elim Pinl Pinr (λx, ua (Pglue x)) y

  protected definition elim_type_on [reducible] (y : pushout) (Pinl : BL → Type)
    (Pinr : TR → Type) (Pglue : Π(x : TL), Pinl (f x) ≃ Pinr (g x)) : Type :=
  elim_type Pinl Pinr Pglue y

  theorem elim_type_glue (Pinl : BL → Type) (Pinr : TR → Type)
    (Pglue : Π(x : TL), Pinl (f x) ≃ Pinr (g x)) (y : pushout) (x : TL)
    : transport (elim_type Pinl Pinr Pglue) (glue x) = Pglue x :=
  by rewrite [tr_eq_cast_ap_fn,↑elim_type,elim_glue];apply cast_ua_fn

end



  namespace test
    open pushout equiv is_equiv unit bool
    private definition unit_of_empty (u : empty) : unit := star

    example : pushout unit_of_empty unit_of_empty ≃ bool :=
    begin
      fapply equiv.MK,
      { intro x, fapply (pushout.rec_on _ _ x),
          intro u, exact ff,
          intro u, exact tt,
          intro c, cases c},
      { intro b, cases b,
          exact (inl _ _ ⋆),
          exact (inr _ _ ⋆)},
      { intro b, cases b, esimp, esimp},
      { intro x, fapply (pushout.rec_on _ _ x),
          intro u, cases u, esimp,
          intro u, cases u, esimp,
          intro c, cases c},
    end

  end test
end pushout
