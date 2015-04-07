/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: hit.colimit
Authors: Floris van Doorn

Colimits.
-/

/- The hit colimit is primitive, declared in init.hit. -/

open eq colimit colimit.diagram function

namespace colimit

  protected definition elim [D : diagram] {P : Type} (Pincl : Π⦃i : Iob⦄ (x : ob i), P)
    (Pglue : Π(j : Ihom) (x : ob (dom j)), Pincl (hom j x) = Pincl x) : colimit D → P :=
  rec Pincl (λj x, !tr_constant ⬝ Pglue j x)

  protected definition elim_on [reducible] [D : diagram] {P : Type} (y : colimit D)
    (Pincl : Π⦃i : Iob⦄ (x : ob i), P)
    (Pglue : Π(j : Ihom) (x : ob (dom j)), Pincl (hom j x) = Pincl x) : P :=
  elim Pincl Pglue y

  definition elim_cglue [D : diagram] {P : Type} (Pincl : Π⦃i : Iob⦄ (x : ob i), P)
    (Pglue : Π(j : Ihom) (x : ob (dom j)), Pincl (hom j x) = Pincl x) {j : Ihom} (x : ob (dom j)) :
      ap (elim Pincl Pglue) (cglue j x) = sorry ⬝ Pglue j x ⬝ sorry :=
  sorry

end colimit

/- definition of a sequential colimit -/
open nat

namespace seq_colimit
context
  parameters {A : ℕ → Type} (f : Π⦃n⦄, A n → A (succ n))
  variables {n : ℕ} (a : A n)

  definition seq_diagram : diagram :=
  diagram.mk ℕ ℕ A id succ f
  local attribute seq_diagram [instance]

  -- TODO: define this in root namespace
  definition seq_colim {A : ℕ → Type} (f : Π⦃n⦄, A n → A (succ n)) : Type :=
  colimit seq_diagram

  definition inclusion : seq_colim f :=
  @colimit.inclusion _ _ a

  abbreviation sι := @inclusion

  definition glue : sι (f a) = sι a :=
  @cglue _ _ a

  protected definition rec [reducible] {P : seq_colim f → Type}
    (Pincl : Π⦃n : ℕ⦄ (a : A n), P (sι a))
    (Pglue : Π(n : ℕ) (a : A n), glue a ▹ Pincl (f a) = Pincl a) : Πaa, P aa :=
  @colimit.rec _ _ Pincl Pglue

  protected definition rec_on [reducible] {P : seq_colim f → Type} (aa : seq_colim f)
    (Pincl : Π⦃n : ℕ⦄ (a : A n), P (sι a))
    (Pglue : Π⦃n : ℕ⦄ (a : A n), glue a ▹ Pincl (f a) = Pincl a)
      : P aa :=
  rec Pincl Pglue aa

  protected definition elim {P : Type} (Pincl : Π⦃n : ℕ⦄ (a : A n), P)
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) = Pincl a) : seq_colim f → P :=
  @colimit.elim _ _ Pincl Pglue

  protected definition elim_on [reducible] {P : Type} (aa : seq_colim f)
    (Pincl : Π⦃n : ℕ⦄ (a : A n), P)
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) = Pincl a) : P :=
  elim Pincl Pglue aa

  definition rec_glue {P : seq_colim f → Type} (Pincl : Π⦃n : ℕ⦄ (a : A n), P (sι a))
    (Pglue : Π⦃n : ℕ⦄ (a : A n), glue a ▹ Pincl (f a) = Pincl a) {n : ℕ} (a : A n)
      : apD (rec Pincl Pglue) (glue a) = sorry ⬝ Pglue a ⬝ sorry :=
  sorry

  definition elim_glue {P : Type} (Pincl : Π⦃n : ℕ⦄ (a : A n), P)
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) = Pincl a) {n : ℕ} (a : A n)
      : ap (elim Pincl Pglue) (glue a) = sorry ⬝ Pglue a ⬝ sorry :=
  sorry

end
end seq_colimit
