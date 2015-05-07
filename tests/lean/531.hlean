/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: init.hit
Authors: Floris van Doorn

Declaration of hits
-/

structure diagram [class] :=
  (Iob : Type)
  (Ihom : Type)
  (ob : Iob → Type)
  (dom cod : Ihom → Iob)
  (hom : Π(j : Ihom), ob (dom j) → ob (cod j))

open eq diagram

-- structure col (D : diagram) :=
--   (incl : Π{i : Iob}, ob i)
--   (eq_endpoint : Π{j : Ihom} (x : ob (dom j)), ob (cod j))
-- set_option pp.universes true
-- check @diagram
-- check @col

constant colimit.{u v w} : diagram.{u v w} → Type.{max u v w}

namespace colimit

  constant inclusion : Π [D : diagram] {i : Iob}, ob i → colimit D
  abbreviation ι := @inclusion

  constant cglue : Π [D : diagram] (j : Ihom) (x : ob (dom j)), ι (hom j x) = ι x

  /-protected-/ constant rec : Π [D : diagram] {P : colimit D → Type}
    (Pincl : Π⦃i : Iob⦄ (x : ob i), P (ι x))
    (Pglue : Π(j : Ihom) (x : ob (dom j)), cglue j x ▸ Pincl (hom j x) = Pincl x)
      (y : colimit D), P y

  -- {P : my_colim f → Type} (Hinc : Π⦃n : ℕ⦄ (a : A n), P (inc f a))
  -- (Heq : Π(n : ℕ) (a : A n), inc_eq f a ▸ Hinc (f a) = Hinc a) : Πaa, P aa
  -- init_hit

  definition comp_incl [D : diagram] {P : colimit D → Type}
    (Pincl : Π⦃i : Iob⦄ (x : ob i), P (ι x))
    (Pglue : Π(j : Ihom) (x : ob (dom j)), cglue j x ▸ Pincl (hom j x) = Pincl x)
      {i : Iob} (x : ob i) : rec Pincl Pglue (ι x) = Pincl x :=
  sorry --idp

  --set_option pp.notation false
  definition comp_cglue [D : diagram] {P : colimit D → Type}
    (Pincl : Π⦃i : Iob⦄ (x : ob i), P (ι x))
    (Pglue : Π(j : Ihom) (x : ob (dom j)), cglue j x ▸ Pincl (hom j x) = Pincl x)
      {j : Ihom} (x : ob (dom j)) : apd (rec Pincl Pglue) (cglue j x) = sorry ⬝ Pglue j x ⬝ sorry :=
  --the sorry's in the statement can be removed when comp_incl is definitional
  sorry --idp

  protected definition rec_on [D : diagram] {P : colimit D → Type} (y : colimit D)
    (Pincl : Π⦃i : Iob⦄ (x : ob i), P (ι x))
    (Pglue : Π(j : Ihom) (x : ob (dom j)), cglue j x ▸ Pincl (hom j x) = Pincl x) : P y :=
  colimit.rec Pincl Pglue y

end colimit

open colimit bool

namespace pushout
section

universe u
parameters {TL BL TR : Type.{u}} (f : TL → BL) (g : TL → TR)

  inductive pushout_ob :=
  | tl : pushout_ob
  | bl : pushout_ob
  | tr : pushout_ob

  open pushout_ob

  definition pushout_diag [reducible] : diagram :=
  diagram.mk pushout_ob
             bool
             (λi, pushout_ob.rec_on i TL BL TR)
             (λj, bool.rec_on j tl tl)
             (λj, bool.rec_on j bl tr)
             (λj, bool.rec_on j f  g)

  local notation `D` := pushout_diag
  -- open bool
  -- definition pushout_diag : diagram :=
  -- diagram.mk pushout_ob
  --            bool
  --            (λi, match i with | tl := TL | tr := TR | bl := BL end)
  --            (λj, match j with | tt := tl | ff := tl end)
  --            (λj, match j with | tt := bl | ff := tr end)
  --            (λj, match j with | tt := f  | ff := g  end)

  definition pushout := colimit pushout_diag
  local attribute pushout_diag [instance]

  definition inl (x : BL) : pushout :=
  @ι _ _ x

  definition inr (x : TR) : pushout :=
  @ι _ _ x

  definition coherence (x : TL) : inl (f x) = @ι _ _ x :=
  @cglue _ _ x

  definition glue (x : TL) : inl (f x) = inr (g x) :=
  @cglue _ _ x ⬝ (@cglue _ _ x)⁻¹

  set_option pp.notation false
  protected theorem rec {P : pushout → Type} --make def
    (Pinl : Π(x : BL), P (inl x))
    (Pinr : Π(x : TR), P (inr x))
    (Pglue : Π(x : TL), glue x ▸ Pinl (f x) = Pinr (g x))
      (y : pushout) : P y :=
  begin
    fapply (@colimit.rec_on _ _ y),
    { intros [i, x], cases i,
       exact (coherence x ▸ Pinl (f x)),
       apply Pinl,
       apply Pinr},
    { intros [j, x], cases j,
        exact idp,
      esimp [pushout_ob.cases_on],
      apply concat, rotate 1, apply (idpath (coherence x ▸ Pinl (f x))),
      apply concat, apply (ap (transport _ _)), apply (idpath (Pinr (g x))),
      apply eq_tr_of_inv_tr_eq,
      rewrite -{(transport (λ (x : pushout), P x) (inverse (coherence x)) (transport P (@cglue _ tt x) (Pinr (g x))))}con_tr,
      apply sorry
    }
  end

example
{P : pushout → Type}
{Pinl : Π (x : BL), P (inl x)}
{Pinr : Π (x : TR), P (inr x)}
{Pglue : Π (x : TL), eq (transport (λ (x : pushout), P x) (glue x) (Pinl (f x))) (Pinr (g x))}
{y : pushout}
{x : @ob _ (@dom _ tt)}
: eq (transport (λ (x : pushout), P x) (inverse (coherence x)) (transport P (@cglue _ tt x) (Pinr (g x))))
    (Pinl (f x)) :=
begin
rewrite -{(transport (λ (x : pushout), P x) (inverse (coherence x)) (transport P (@cglue _ tt x) (Pinr (g x))))}con_tr,
apply sorry
end

exit
