/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

import algebra.category.constructions .constructions types.function arity

open category functor nat_trans eq is_trunc iso equiv prod trunc function

namespace category
  variables {C D : Precategory} {F : C ⇒ D}

  -- do we want to have a structure "is_adjoint" and define
  -- structure is_left_adjoint (F : C ⇒ D) :=
  --   (right_adjoint : D ⇒ C) -- G
  --   (is_adjoint : adjoint F right_adjoint)

  structure is_left_adjoint [class] (F : C ⇒ D) :=
    (G : D ⇒ C)
    (η : functor.id ⟹ G ∘f F)
    (ε : F ∘f G ⟹ functor.id)
    (H : Π(c : C), (ε (F c)) ∘ (F (η c)) = ID (F c))
    (K : Π(d : D), (G (ε d)) ∘ (η (G d)) = ID (G d))

  abbreviation right_adjoint := @is_left_adjoint.G
  abbreviation unit          := @is_left_adjoint.η
  abbreviation counit        := @is_left_adjoint.ε

  -- structure is_left_adjoint [class] (F : C ⇒ D) :=
  --   (right_adjoint : D ⇒ C) -- G
  --   (unit : functor.id ⟹ right_adjoint ∘f F) -- η
  --   (counit : F ∘f right_adjoint ⟹ functor.id) -- ε
  --   (H : Π(c : C), (counit (F c)) ∘ (F (unit c)) = ID (F c))
  --   (K : Π(d : D), (right_adjoint (counit d)) ∘ (unit (right_adjoint d)) = ID (right_adjoint d))

  structure is_equivalence [class] (F : C ⇒ D) extends is_left_adjoint F :=
    mk' ::
    (is_iso_unit : is_iso η)
    (is_iso_counit : is_iso ε)

  structure equivalence (C D : Precategory) :=
    (to_functor : C ⇒ D)
    (struct : is_equivalence to_functor)

  --TODO: review and change
  --TODO: make some or all of these structures?
  definition faithful (F : C ⇒ D) :=
  Π⦃c c' : C⦄ (f f' : c ⟶ c'), F f = F f' → f = f'

  definition full (F : C ⇒ D) := Π⦃c c' : C⦄ (g : F c ⟶ F c'), ∃(f : c ⟶ c'), F f = g

  definition fully_faithful [reducible] (F : C ⇒ D) :=
  Π⦃c c' : C⦄, is_equiv (@(to_fun_hom F) c c')

  definition split_essentially_surjective (F : C ⇒ D) :=
  Π⦃d : D⦄, Σ(c : C), F c ≅ d

  definition essentially_surjective (F : C ⇒ D) :=
  Π⦃d : D⦄, ∃(c : C), F c ≅ d

  definition is_weak_equivalence (F : C ⇒ D) :=
  fully_faithful F × essentially_surjective F

  definition is_isomorphism (F : C ⇒ D) :=
  fully_faithful F × is_equiv (to_fun_ob F)

  structure isomorphism (C D : Precategory) :=
    (to_functor : C ⇒ D)
    (struct : is_isomorphism to_functor)
  --   infix `⊣`:55 := adjoint

  infix `⋍`:25 := equivalence -- \backsimeq or \equiv
  infix `≌`:25 := isomorphism -- \backcong or \iso

/-
  definition is_hprop_is_left_adjoint {C : Category} {D : Precategory} (F : C ⇒ D)
    : is_hprop (is_left_adjoint F) :=
  begin
    apply is_hprop.mk,
    intro G G', cases G with G η ε H K, cases G' with G' η' ε' H' K',
    fapply (apd011111 is_left_adjoint.mk),
    { fapply functor_eq,
      { intro d, apply eq_of_iso, fapply iso.MK,
        { exact (G' (ε d) ∘ η' (G d))},
        { exact (G (ε' d) ∘ η (G' d))},
        { apply sorry /-rewrite [assoc, -{((G (ε' d)) ∘ (η (G' d))) ∘ (G' (ε d))}(assoc)],-/
--        apply concat, apply (ap (λc, c ∘ η' _)), rewrite -assoc, apply idp
},
-- rewrite [-nat_trans.assoc] apply sorry
---assoc (G (ε' d)) (η (G' d)) (G' (ε d))
        { apply sorry}},
      { apply sorry},
},
    { apply sorry},
    { apply sorry},
    { apply is_hprop.elim},
    { apply is_hprop.elim},
  end

  definition is_equivalence.mk (F : C ⇒ D) (G : D ⇒ C) (η : G ∘f F ≅ functor.id)
    (ε : F ∘f G ≅ functor.id) : is_equivalence F :=
  sorry

  definition full_of_fully_faithful (H : fully_faithful F) : full F :=
  sorry --  λc c' g, exists.intro ((@(to_fun_hom F) c c')⁻¹ g) _

  definition faithful_of_fully_faithful (H : fully_faithful F) : faithful F :=
  λc c' f f' p, is_injective_of_is_embedding p

  definition fully_faithful_of_full_of_faithful (H : faithful F) (K : full F) : fully_faithful F :=
  sorry

  definition fully_faithful_equiv (F : C ⇒ D) : fully_faithful F ≃ (faithful F × full F) :=
  sorry

  definition is_equivalence_equiv (F : C ⇒ D)
    : is_equivalence F ≃ (fully_faithful F × split_essentially_surjective F) :=
  sorry

  definition is_hprop_is_weak_equivalence (F : C ⇒ D) : is_hprop (is_weak_equivalence F) :=
  sorry

  definition is_hprop_is_equivalence {C D : Category} (F : C ⇒ D) : is_hprop (is_equivalence F) :=
  sorry

  definition is_equivalence_equiv_is_weak_equivalence {C D : Category} (F : C ⇒ D)
    : is_equivalence F ≃ is_weak_equivalence F :=
  sorry

  definition is_hprop_is_isomorphism (F : C ⇒ D) : is_hprop (is_isomorphism F) :=
  sorry

  definition is_isomorphism_equiv1 (F : C ⇒ D) : is_equivalence F
    ≃ Σ(G : D ⇒ C) (η : functor.id = G ∘f F) (ε : F ∘f G = functor.id),
        sorry ▸ ap (λ(H : C ⇒ C), F ∘f H) η = ap (λ(H : D ⇒ D), H ∘f F) ε⁻¹ :=
  sorry

  definition is_isomorphism_equiv2 (F : C ⇒ D) : is_equivalence F
    ≃ ∃(G : D ⇒ C), functor.id = G ∘f F × F ∘f G = functor.id :=
  sorry

  definition is_equivalence_of_isomorphism (H : is_isomorphism F) : is_equivalence F :=
  sorry

  definition is_isomorphism_of_is_equivalence {C D : Category} {F : C ⇒ D} (H : is_equivalence F)
    : is_isomorphism F :=
  sorry

  definition isomorphism_of_eq {C D : Precategory} (p : C = D) : C ≌ D :=
  sorry

  definition is_equiv_isomorphism_of_eq (C D : Precategory) : is_equiv (@isomorphism_of_eq C D) :=
  sorry

  definition equivalence_of_eq {C D : Precategory} (p : C = D) : C ⋍ D :=
  sorry

  definition is_equiv_equivalence_of_eq (C D : Category) : is_equiv (@equivalence_of_eq C D) :=
  sorry
-/
end category
