/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.precategory.yoneda
Authors: Floris van Doorn
-/

import algebra.category.basic .constructions

open category functor nat_trans eq is_trunc iso equiv prod

variables {C D : Precategory} {F : C ⇒ D}

-- structure adjoint (F : C ⇒ D) (G : D ⇒ C) :=
--   (unit : functor.id ⟹ G ∘f F) -- η
--   (counit : F ∘f G ⟹ functor.id) -- ε
--   (H : (counit ∘nf F) ∘n (nat_trans_of_eq !functor.assoc) ∘n (F ∘fn unit)
--     = nat_trans_of_eq !functor.comp_id_eq_id_comp)
--   (K : (G ∘fn counit) ∘n (nat_trans_of_eq !functor.assoc⁻¹) ∘n (unit ∘nf G)
--     = nat_trans_of_eq !functor.comp_id_eq_id_comp⁻¹)

-- structure is_left_adjoint (F : C ⇒ D) :=
--   (right_adjoint : D ⇒ C) -- G
--   (is_adjoint : adjoint F right_adjoint)

structure is_left_adjoint (F : C ⇒ D) :=
  (right_adjoint : D ⇒ C) -- G
  (unit : functor.id ⟹ right_adjoint ∘f F) -- η
  (counit : F ∘f right_adjoint ⟹ functor.id) -- ε
  (H : (counit ∘nf F) ∘n (nat_trans_of_eq !functor.assoc) ∘n (F ∘fn unit)
    = nat_trans_of_eq !functor.comp_id_eq_id_comp)
  (K : (right_adjoint ∘fn counit) ∘n (nat_trans_of_eq !functor.assoc⁻¹) ∘n (unit ∘nf right_adjoint)
    = nat_trans_of_eq !functor.comp_id_eq_id_comp⁻¹)

structure is_equivalence (F : C ⇒ D) extends is_left_adjoint F :=
  mk' ::
  (is_iso_unit : is_iso unit)
  (is_iso_counit : is_iso counit)

structure equivalence (C D : Precategory) :=
  (to_functor : C ⇒ D)
  (struct : is_equivalence to_functor)

--TODO: review and change
--TODO: make some or all of these structures?
definition faithful (F : C ⇒ D) :=
Π⦃c c' : C⦄, (Π(f f' : c ⟶ c'), to_fun_hom F f = to_fun_hom F f' → f = f')

definition full (F : C ⇒ D) := Π⦃c c' : C⦄ (g : F c ⟶ F c'), Σ(f : c ⟶ c'), F f = g --merely

definition fully_faithful (F : C ⇒ D) := Π⦃c c' : C⦄, is_equiv (@to_fun_hom _ _ F c c')

definition split_essentially_surjective (F : C ⇒ D) :=
Π⦃d : D⦄, Σ(c : C), F c ≅ d

definition essentially_surjective (F : C ⇒ D) :=
Π⦃d : D⦄, Σ(c : C), F c ≅ d --merely

definition is_weak_equivalence (F : C ⇒ D) :=
fully_faithful F × essentially_surjective F

definition is_isomorphism (F : C ⇒ D) :=
fully_faithful F × is_equiv (to_fun_ob F)

structure isomorphism (C D : Precategory) :=
  (to_functor : C ⇒ D)
  (struct : is_isomorphism to_functor)

namespace category

  infix `⋍`:25 := equivalence -- \backsimeq
  infix `≌`:25 := isomorphism -- \backcong
  --TODO: add shortcuts for Σ⋍≌▹

  definition is_hprop_is_left_adjoint {C : Category} {D : Precategory} (F : C ⇒ D)
    : is_hprop (is_left_adjoint F) :=
  sorry

  definition is_equivalence.mk (F : C ⇒ D) (G : D ⇒ C) (η : G ∘f F ≅ functor.id)
    (ε : F ∘f G ≅ functor.id) : is_equivalence F :=
  sorry

  definition full_of_fully_faithful (H : fully_faithful F) : full F :=
  sorry

  definition faithful_of_fully_faithful (H : fully_faithful F) : faithful F :=
  sorry

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
        sorry ▹ ap (λ(H : C ⇒ C), F ∘f H) η = ap (λ(H : D ⇒ D), H ∘f F) ε⁻¹ :=
  sorry

  definition is_isomorphism_equiv2 (F : C ⇒ D) : is_equivalence F
    ≃ Σ/-MERELY-/(G : D ⇒ C), functor.id = G ∘f F × F ∘f G = functor.id :=
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

end category
