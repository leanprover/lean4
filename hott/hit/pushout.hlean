/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: hit.pushout
Authors: Floris van Doorn

Declaration of the pushout
-/

import .type_quotient

open type_quotient eq sum

namespace pushout
context

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
  eq_of_rel (Rmk f g x)

  protected definition rec {P : pushout → Type} (Pinl : Π(x : BL), P (inl x))
    (Pinr : Π(x : TR), P (inr x)) (Pglue : Π(x : TL), glue x ▹ Pinl (f x) = Pinr (g x))
      (y : pushout) : P y :=
  begin
    fapply (type_quotient.rec_on y),
    { intro a, cases a,
       apply Pinl,
       apply Pinr},
    { intros [a, a', H], cases H, apply Pglue}
  end

  protected definition rec_on [reducible] {P : pushout → Type} (y : pushout)
    (Pinl : Π(x : BL), P (inl x)) (Pinr : Π(x : TR), P (inr x))
    (Pglue : Π(x : TL), glue x ▹ Pinl (f x) = Pinr (g x)) : P y :=
  rec Pinl Pinr Pglue y

  --these definitions are needed until we have them definitionally
  definition rec_inl {P : pushout → Type} (Pinl : Π(x : BL), P (inl x))
    (Pinr : Π(x : TR), P (inr x)) (Pglue : Π(x : TL), glue x ▹ Pinl (f x) = Pinr (g x))
      (x : BL) : rec Pinl Pinr Pglue (inl x) = Pinl x :=
  rec_class_of _ _ _ --idp

  definition rec_inr {P : pushout → Type} (Pinl : Π(x : BL), P (inl x))
    (Pinr : Π(x : TR), P (inr x)) (Pglue : Π(x : TL), glue x ▹ Pinl (f x) = Pinr (g x))
      (x : TR) : rec Pinl Pinr Pglue (inr x) = Pinr x :=
  rec_class_of _ _ _ --idp

  protected definition elim {P : Type} (Pinl : BL → P) (Pinr : TR → P)
    (Pglue : Π(x : TL), Pinl (f x) = Pinr (g x)) (y : pushout) : P :=
  rec Pinl Pinr (λx, !tr_constant ⬝ Pglue x) y

  protected definition elim_on [reducible] {P : Type} (Pinl : BL → P) (y : pushout)
    (Pinr : TR → P) (Pglue : Π(x : TL), Pinl (f x) = Pinr (g x)) : P :=
  elim Pinl Pinr Pglue y

  definition rec_glue {P : pushout → Type} (Pinl : Π(x : BL), P (inl x))
    (Pinr : Π(x : TR), P (inr x)) (Pglue : Π(x : TL), glue x ▹ Pinl (f x) = Pinr (g x))
      (x : TL) : apD (rec Pinl Pinr Pglue) (glue x) = sorry ⬝ Pglue x ⬝ sorry :=
  sorry

  definition elim_glue {P : Type} (Pinl : BL → P) (Pinr : TR → P)
    (Pglue : Π(x : TL), Pinl (f x) = Pinr (g x)) (y : pushout) (x : TL)
    : ap (elim Pinl Pinr Pglue) (glue x) = sorry ⬝ Pglue x ⬝ sorry :=
  sorry


end

  open pushout equiv is_equiv unit bool

  namespace test
    definition unit_of_empty (u : empty) : unit := star

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
      { intro b, cases b, apply rec_inl, apply rec_inr},
      { intro x, fapply (pushout.rec_on _ _ x),
          intro u, cases u, rewrite [↑function.compose,↑pushout.rec_on,rec_inl],
          intro u, cases u, rewrite [↑function.compose,↑pushout.rec_on,rec_inr],
          intro c, cases c},
    end

  end test
end pushout
