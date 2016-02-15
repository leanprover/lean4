/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Attributes of functors (full, faithful, split essentially surjective, ...)

Adjoint functors, isomorphisms and equivalences have their own file
-/

import ..constructions.functor function arity

open eq functor trunc prod is_equiv iso equiv function is_trunc

namespace category
  variables {C D E : Precategory} {F : C ⇒ D} {G : D ⇒ C}

  definition faithful [class] (F : C ⇒ D) := Π⦃c c' : C⦄ ⦃f f' : c ⟶ c'⦄, F f = F f' → f = f'
  definition full [class] (F : C ⇒ D) := Π⦃c c' : C⦄, is_surjective (@(to_fun_hom F) c c')
  definition fully_faithful [class] (F : C ⇒ D) := Π(c c' : C), is_equiv (@(to_fun_hom F) c c')
  definition split_essentially_surjective [class] (F : C ⇒ D) := Π(d : D), Σ(c : C), F c ≅ d
  definition essentially_surjective [class] (F : C ⇒ D) := Π(d : D), ∃(c : C), F c ≅ d
  definition is_weak_equivalence [class] (F : C ⇒ D) :=
  fully_faithful F × essentially_surjective F

  definition is_equiv_of_fully_faithful [instance] [reducible] (F : C ⇒ D)
    [H : fully_faithful F] (c c' : C) : is_equiv (@(to_fun_hom F) c c') :=
  !H

  definition hom_inv [reducible] (F : C ⇒ D) [H : fully_faithful F] (c c' : C) (f : F c ⟶ F c')
    : c ⟶ c' :=
  (to_fun_hom F)⁻¹ᶠ f

  definition reflect_is_iso [constructor] (F : C ⇒ D) [H : fully_faithful F] {c c' : C}
    (f : c ⟶ c') [H : is_iso (F f)] : is_iso f :=
  begin
    fconstructor,
    { exact (to_fun_hom F)⁻¹ᶠ (F f)⁻¹},
    { apply eq_of_fn_eq_fn' (to_fun_hom F),
      rewrite [respect_comp,right_inv (to_fun_hom F),respect_id,left_inverse]},
    { apply eq_of_fn_eq_fn' (to_fun_hom F),
      rewrite [respect_comp,right_inv (to_fun_hom F),respect_id,right_inverse]},
  end

  definition reflect_iso [constructor] (F : C ⇒ D) [H : fully_faithful F] {c c' : C}
    (f : F c ≅ F c') : c ≅ c' :=
  begin
    fconstructor,
    { exact (to_fun_hom F)⁻¹ᶠ f},
    { assert H : is_iso (F ((to_fun_hom F)⁻¹ᶠ f)),
      { have H' : is_iso (to_hom f), from _, exact (right_inv (to_fun_hom F) (to_hom f))⁻¹ ▸ H'},
      exact reflect_is_iso F _},
  end

  theorem reflect_inverse (F : C ⇒ D) [H : fully_faithful F] {c c' : C} (f : c ⟶ c')
    [H : is_iso f] : (to_fun_hom F)⁻¹ᶠ (F f)⁻¹ = f⁻¹ :=
  inverse_eq_inverse (idp : to_hom (@(iso.mk f) (reflect_is_iso F f)) = f)

  definition hom_equiv_F_hom_F [constructor] (F : C ⇒ D)
    [H : fully_faithful F] (c c' : C) : (c ⟶ c') ≃ (F c ⟶ F c') :=
  equiv.mk _ !H

  definition iso_of_F_iso_F (F : C ⇒ D)
    [H : fully_faithful F] (c c' : C) (g : F c ≅ F c') : c ≅ c' :=
  begin
    induction g with g G, induction G with h p q, fapply iso.MK,
      { rexact (to_fun_hom F)⁻¹ᶠ g},
      { rexact (to_fun_hom F)⁻¹ᶠ h},
      { exact abstract begin
        apply eq_of_fn_eq_fn' (to_fun_hom F),
        rewrite [respect_comp, respect_id,
                 right_inv (to_fun_hom F), right_inv (to_fun_hom F), p],
        end end},
      { exact abstract begin
        apply eq_of_fn_eq_fn' (to_fun_hom F),
        rewrite [respect_comp, respect_id,
                 right_inv (to_fun_hom F), right_inv (@(to_fun_hom F) c' c), q],
        end end}
  end

  definition iso_equiv_F_iso_F [constructor] (F : C ⇒ D)
    [H : fully_faithful F] (c c' : C) : (c ≅ c') ≃ (F c ≅ F c') :=
  begin
    fapply equiv.MK,
    { exact to_fun_iso F},
    { apply iso_of_F_iso_F},
    { exact abstract begin
      intro f, induction f with f F', induction F' with g p q, apply iso_eq,
      esimp [iso_of_F_iso_F], apply right_inv end end},
    { exact abstract begin
      intro f, induction f with f F', induction F' with g p q, apply iso_eq,
      esimp [iso_of_F_iso_F], apply right_inv end end},
  end

  definition full_of_fully_faithful [instance] (F : C ⇒ D) [H : fully_faithful F] : full F :=
  λc c' g, tr (fiber.mk ((@(to_fun_hom F) c c')⁻¹ᶠ g) !right_inv)

  definition faithful_of_fully_faithful [instance] (F : C ⇒ D) [H : fully_faithful F]
    : faithful F :=
  λc c' f f' p, is_injective_of_is_embedding p

  definition is_embedding_of_faithful [instance] (F : C ⇒ D) [H : faithful F] (c c' : C)
    : is_embedding (to_fun_hom F : c ⟶ c' → F c ⟶ F c') :=
  begin
    apply is_embedding_of_is_injective,
    apply H
  end

  definition is_surjective_of_full [instance] (F : C ⇒ D) [H : full F] (c c' : C)
    : is_surjective (to_fun_hom F : c ⟶ c' → F c ⟶ F c') :=
  @H c c'

  definition fully_faithful_of_full_of_faithful (H : faithful F) (K : full F)
    : fully_faithful F :=
  begin
    intro c c',
    apply is_equiv_of_is_surjective_of_is_embedding,
  end

  theorem is_prop_fully_faithful [instance] (F : C ⇒ D) : is_prop (fully_faithful F) :=
  by unfold fully_faithful; exact _

  theorem is_prop_full [instance] (F : C ⇒ D) : is_prop (full F) :=
  by unfold full; exact _

  theorem is_prop_faithful [instance] (F : C ⇒ D) : is_prop (faithful F) :=
  by unfold faithful; exact _

  theorem is_prop_essentially_surjective [instance] (F : C ⇒ D)
    : is_prop (essentially_surjective F) :=
  by unfold essentially_surjective; exact _

  theorem is_prop_is_weak_equivalence [instance] (F : C ⇒ D) : is_prop (is_weak_equivalence F) :=
  by unfold is_weak_equivalence; exact _

  definition fully_faithful_equiv (F : C ⇒ D) : fully_faithful F ≃ (faithful F × full F) :=
  equiv_of_is_prop (λH, (faithful_of_fully_faithful F, full_of_fully_faithful F))
                    (λH, fully_faithful_of_full_of_faithful (pr1 H) (pr2 H))

/- alternative proof using direct calculation with equivalences

  definition fully_faithful_equiv (F : C ⇒ D) : fully_faithful F ≃ (faithful F × full F) :=
  calc
        fully_faithful F
      ≃ (Π(c c' : C), is_embedding (to_fun_hom F) × is_surjective (to_fun_hom F))
        : pi_equiv_pi_right (λc, pi_equiv_pi_right
            (λc', !is_equiv_equiv_is_embedding_times_is_surjective))
  ... ≃ (Π(c : C), (Π(c' : C), is_embedding  (to_fun_hom F)) ×
                   (Π(c' : C), is_surjective (to_fun_hom F)))
        : pi_equiv_pi_right (λc, !equiv_prod_corec)
  ... ≃ (Π(c c' : C), is_embedding (to_fun_hom F)) × full F
        : equiv_prod_corec
  ... ≃ faithful F × full F
        : prod_equiv_prod_right (pi_equiv_pi_right (λc, pi_equiv_pi_right
            (λc', !is_embedding_equiv_is_injective)))
-/

end category
