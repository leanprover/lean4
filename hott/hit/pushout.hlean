/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Declaration of the pushout
-/

import .quotient

open quotient eq sum equiv equiv.ops

namespace pushout
section

parameters {TL BL TR : Type} (f : TL → BL) (g : TL → TR)

  local abbreviation A := BL + TR
  inductive pushout_rel : A → A → Type :=
  | Rmk : Π(x : TL), pushout_rel (inl (f x)) (inr (g x))
  open pushout_rel
  local abbreviation R := pushout_rel

  definition pushout : Type := quotient R -- TODO: define this in root namespace

  definition inl (x : BL) : pushout :=
  class_of R (inl x)

  definition inr (x : TR) : pushout :=
  class_of R (inr x)

  definition glue (x : TL) : inl (f x) = inr (g x) :=
  eq_of_rel pushout_rel (Rmk f g x)

  protected definition rec {P : pushout → Type} (Pinl : Π(x : BL), P (inl x))
    (Pinr : Π(x : TR), P (inr x)) (Pglue : Π(x : TL), Pinl (f x) =[glue x] Pinr (g x))
      (y : pushout) : P y :=
  begin
    induction y,
    { cases a,
        apply Pinl,
        apply Pinr},
    { cases H, apply Pglue}
  end

  protected definition rec_on [reducible] {P : pushout → Type} (y : pushout)
    (Pinl : Π(x : BL), P (inl x)) (Pinr : Π(x : TR), P (inr x))
    (Pglue : Π(x : TL), Pinl (f x) =[glue x] Pinr (g x)) : P y :=
  rec Pinl Pinr Pglue y

  theorem rec_glue {P : pushout → Type} (Pinl : Π(x : BL), P (inl x))
    (Pinr : Π(x : TR), P (inr x)) (Pglue : Π(x : TL), Pinl (f x) =[glue x] Pinr (g x))
      (x : TL) : apdo (rec Pinl Pinr Pglue) (glue x) = Pglue x :=
  !rec_eq_of_rel

  protected definition elim {P : Type} (Pinl : BL → P) (Pinr : TR → P)
    (Pglue : Π(x : TL), Pinl (f x) = Pinr (g x)) (y : pushout) : P :=
  rec Pinl Pinr (λx, pathover_of_eq (Pglue x)) y

  protected definition elim_on [reducible] {P : Type} (y : pushout) (Pinl : BL → P)
    (Pinr : TR → P) (Pglue : Π(x : TL), Pinl (f x) = Pinr (g x)) : P :=
  elim Pinl Pinr Pglue y

  theorem elim_glue {P : Type} (Pinl : BL → P) (Pinr : TR → P)
    (Pglue : Π(x : TL), Pinl (f x) = Pinr (g x)) (x : TL)
    : ap (elim Pinl Pinr Pglue) (glue x) = Pglue x :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant (glue x)),
    rewrite [▸*,-apdo_eq_pathover_of_eq_ap,↑pushout.elim,rec_glue],
  end

  protected definition elim_type (Pinl : BL → Type) (Pinr : TR → Type)
    (Pglue : Π(x : TL), Pinl (f x) ≃ Pinr (g x)) (y : pushout) : Type :=
  elim Pinl Pinr (λx, ua (Pglue x)) y

  protected definition elim_type_on [reducible] (y : pushout) (Pinl : BL → Type)
    (Pinr : TR → Type) (Pglue : Π(x : TL), Pinl (f x) ≃ Pinr (g x)) : Type :=
  elim_type Pinl Pinr Pglue y

  theorem elim_type_glue (Pinl : BL → Type) (Pinr : TR → Type)
    (Pglue : Π(x : TL), Pinl (f x) ≃ Pinr (g x)) (x : TL)
    : transport (elim_type Pinl Pinr Pglue) (glue x) = Pglue x :=
  by rewrite [tr_eq_cast_ap_fn,↑elim_type,elim_glue];apply cast_ua_fn

end
end pushout

attribute pushout.inl pushout.inr [constructor]
attribute pushout.rec pushout.elim [unfold 10] [recursor 10]
attribute pushout.elim_type [unfold 9]
attribute pushout.rec_on pushout.elim_on [unfold 7]
attribute pushout.elim_type_on [unfold 6]
