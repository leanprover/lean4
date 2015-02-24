-- Copyright (c) 2014 Jakob von Raumer. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Floris van Doorn, Jakob von Raumer

import .basic .morphism types.sigma

open eq precategory sigma sigma.ops equiv is_equiv function is_trunc
open prod

namespace morphism
  variables {ob : Type} [C : precategory ob] include C
  variables {a b c : ob} {g : b ⟶ c} {f : a ⟶ b} {h : b ⟶ a}

  -- "is_iso f" is equivalent to a certain sigma type
  protected definition sigma_char (f : hom a b) :
    (Σ (g : hom b a), (g ∘ f = id) × (f ∘ g = id)) ≃ is_iso f :=
  begin
    fapply (equiv.mk),
      {intro S, apply is_iso.mk,
        exact (pr₁ S.2),
        exact (pr₂ S.2)},
      {fapply adjointify,
        {intro H, cases H with (g, η, ε),
         exact (sigma.mk g (pair η ε))},
        {intro H, cases H, apply idp},
        {intro S, cases S with (g, ηε), cases ηε, apply idp}},
  end

  -- The structure for isomorphism can be characterized up to equivalence
  -- by a sigma type.
  definition sigma_is_iso_equiv ⦃a b : ob⦄ : (Σ (f : hom a b), is_iso f) ≃ (a ≅ b) :=
  begin
    fapply (equiv.mk),
      {intro S, apply isomorphic.mk, apply (S.2)},
      {fapply adjointify,
        {intro p, cases p with (f, H), exact (sigma.mk f H)},
        {intro p, cases p, apply idp},
        {intro S, cases S, apply idp}},
  end

  set_option apply.class_instance false -- disable class instance resolution in the apply tactic

  -- The statement "f is an isomorphism" is a mere proposition
  definition is_hprop_of_is_iso : is_hset (is_iso f) :=
  begin
    apply is_trunc_is_equiv_closed,
      apply (equiv.to_is_equiv (!sigma_char)),
    apply is_trunc_sigma,
      apply (!homH),
    {intro g, apply is_trunc_prod,
      repeat (apply is_trunc_eq; apply is_trunc_succ; apply (!homH))},
  end

  -- The type of isomorphisms between two objects is a set
  definition is_hset_iso : is_hset (a ≅ b) :=
  begin
    apply is_trunc_is_equiv_closed,
      apply (equiv.to_is_equiv (!sigma_is_iso_equiv)),
      apply is_trunc_sigma,
       apply homH,
       {intro f, apply is_hprop_of_is_iso},
  end

  -- In a precategory, equal objects are isomorphic
  definition iso_of_path (p : a = b) : isomorphic a b :=
  eq.rec_on p (isomorphic.mk id)

end morphism
