-- Copyright (c) 2014 Jakob von Raumer. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Floris van Doorn, Jakob von Raumer

import .basic .morphism hott.types.prod

open path precategory sigma sigma.ops equiv is_equiv function truncation
open prod

namespace morphism
  variables {ob : Type} [C : precategory ob] include C
  variables {a b c : ob} {g : b ⟶ c} {f : a ⟶ b} {h : b ⟶ a}

  -- "is_iso f" is equivalent to a certain sigma type
  definition sigma_equiv_of_is_iso (f : hom a b) :
    (Σ (g : hom b a), (g ∘ f ≈ id) × (f ∘ g ≈ id)) ≃ is_iso f :=
  begin
    fapply (equiv.mk),
      intro S, apply is_iso.mk,
          exact (pr₁ S.2),
        exact (pr₂ S.2),
    fapply adjointify,
        intro H, apply (is_iso.rec_on H), intros (g, η, ε),
        exact (dpair g (pair η ε)),
      intro H, apply (is_iso.rec_on H), intros (g, η, ε), apply idp,
    intro S, apply (sigma.rec_on S), intros (g, ηε),
    apply (prod.rec_on ηε), intros (η, ε), apply idp,
  end

  -- The structure for isomorphism can be characterized up to equivalence
  -- by a sigma type.
  definition sigma_is_iso_equiv ⦃a b : ob⦄ : (Σ (f : hom a b), is_iso f) ≃ (a ≅ b) :=
  begin
    fapply (equiv.mk),
      intro S, apply isomorphic.mk, apply (S.2),
      fapply adjointify,
        intro p, apply (isomorphic.rec_on p), intros (f, H),
        exact (dpair f H),
      intro p, apply (isomorphic.rec_on p), intros (f, H), apply idp,
    intro S, apply (sigma.rec_on S), intros (f, H), apply idp,
  end

  -- The statement "f is an isomorphism" is a mere proposition
  definition is_hprop_of_is_iso : is_hset (is_iso f) :=
  begin
    apply trunc_equiv,
      apply (equiv.to_is_equiv (!sigma_equiv_of_is_iso)),
    apply sigma_trunc,
      apply (!homH),
    intro g, apply trunc_prod,
      repeat (apply succ_is_trunc; apply trunc_succ; apply (!homH)),
  end

  -- The type of isomorphisms between two objects is a set
  definition is_hset_iso : is_hset (a ≅ b) :=
  begin
    apply trunc_equiv,
      apply (equiv.to_is_equiv (!sigma_is_iso_equiv)),
    apply sigma_trunc,
      apply homH,
    intro f, apply is_hprop_of_is_iso,
  end

  -- In a precategory, equal objects are isomorphic
  definition iso_of_path (p : a ≈ b) : isomorphic a b :=
  path.rec_on p (isomorphic.mk id)

end morphism
