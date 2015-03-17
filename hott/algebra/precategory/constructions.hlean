/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.precategory.constructions
Authors: Floris van Doorn, Jakob von Raumer

This file contains basic constructions on precategories, including common precategories
-/

import .nat_trans
import types.prod types.sigma types.pi

open eq prod eq eq.ops equiv is_trunc

namespace category
  namespace opposite

  definition opposite [reducible] {ob : Type} (C : precategory ob) : precategory ob :=
  precategory.mk (λ a b, hom b a)
                 (λ a b, !homH)
                 (λ a b c f g, g ∘ f)
                 (λ a, id)
                 (λ a b c d f g h, !assoc⁻¹)
                 (λ a b f, !id_right)
                 (λ a b f, !id_left)

  definition Opposite [reducible] (C : Precategory) : Precategory := precategory.Mk (opposite C)

  infixr `∘op`:60 := @comp _ (opposite _) _ _ _

  variables {C : Precategory} {a b c : C}

  set_option apply.class_instance false -- disable class instance resolution in the apply tactic

  definition compose_op {f : hom a b} {g : hom b c} : f ∘op g = g ∘ f := idp

  -- TODO: Decide whether just to use funext for this theorem or
  --       take the trick they use in Coq-HoTT, and introduce a further
  --       axiom in the definition of precategories that provides thee
  --       symmetric associativity proof.
  definition opposite_opposite' {ob : Type} (C : precategory ob) : opposite (opposite C) = C :=
  begin
    apply (precategory.rec_on C), intros (hom', homH', comp', ID', assoc', id_left', id_right'),
    apply (ap (λassoc'', precategory.mk hom' @homH' comp' ID' assoc'' id_left' id_right')),
    repeat (apply eq_of_homotopy ; intros ),
    apply ap,
    apply (@is_hset.elim), apply !homH',
  end

  definition opposite_opposite : Opposite (Opposite C) = C :=
  (ap (Precategory.mk C) (opposite_opposite' C)) ⬝ !Precategory.eta

  end opposite

  -- Note: Discrete precategory doesn't really make sense in HoTT,
  -- We'll define a discrete _category_ later.
  /-section
  open decidable unit empty
  variables {A : Type} [H : decidable_eq A]
  include H
  definition set_hom (a b : A) := decidable.rec_on (H a b) (λh, unit) (λh, empty)
  theorem set_hom_subsingleton [instance] (a b : A) : subsingleton (set_hom a b) := _
  definition set_compose {a b c : A} (g : set_hom b c) (f : set_hom a b) : set_hom a c :=
  decidable.rec_on
    (H b c)
    (λ Hbc g, decidable.rec_on
      (H a b)
      (λ Hab f, rec_on_true (trans Hab Hbc) ⋆)
      (λh f, empty.rec _ f) f)
    (λh (g : empty), empty.rec _ g) g
  omit H
  definition discrete_precategory (A : Type) [H : decidable_eq A] : precategory A :=
  mk (λa b, set_hom a b)
     (λ a b c g f, set_compose g f)
     (λ a, decidable.rec_on_true rfl ⋆)
     (λ a b c d h g f, @subsingleton.elim (set_hom a d) _ _ _)
     (λ a b f, @subsingleton.elim (set_hom a b) _ _ _)
     (λ a b f, @subsingleton.elim (set_hom a b) _ _ _)
  definition Discrete_category (A : Type) [H : decidable_eq A] := Mk (discrete_category A)
  end
  section
  open unit bool
  definition category_one := discrete_category unit
  definition Category_one := Mk category_one
  definition category_two := discrete_category bool
  definition Category_two := Mk category_two
  end-/

  namespace product
  section
  open prod is_trunc

  definition precategory_prod [reducible] {obC obD : Type} (C : precategory obC) (D : precategory obD)
      : precategory (obC × obD) :=
  precategory.mk (λ a b, hom (pr1 a) (pr1 b) × hom (pr2 a) (pr2 b))
                 (λ a b, !is_trunc_prod)
                 (λ a b c g f, (pr1 g ∘ pr1 f , pr2 g ∘ pr2 f))
                 (λ a, (id, id))
                 (λ a b c d h g f, pair_eq  !assoc    !assoc   )
                 (λ a b f,         prod_eq  !id_left  !id_left )
                 (λ a b f,         prod_eq  !id_right !id_right)

  definition Precategory_prod [reducible] (C D : Precategory) : Precategory :=
  precategory.Mk (precategory_prod C D)

  end
  end product

  namespace ops
    --notation 1 := Category_one
    --notation 2 := Category_two
    postfix `ᵒᵖ`:max := opposite.Opposite
    infixr `×c`:30 := product.Precategory_prod
    --instance [persistent] type_category category_one
    --                      category_two product.prod_category
  end ops

  open ops
  namespace opposite
  open ops functor
  definition opposite_functor [reducible] {C D : Precategory} (F : C ⇒ D) : Cᵒᵖ ⇒ Dᵒᵖ :=
  begin
    apply (@functor.mk (Cᵒᵖ) (Dᵒᵖ)),
      intro a, apply (respect_id F),
      intros, apply (@respect_comp C D)
  end

  end opposite

  namespace product
  section
  open ops functor
  definition prod_functor [reducible] {C C' D D' : Precategory} (F : C ⇒ D) (G : C' ⇒ D') : C ×c C' ⇒ D ×c D' :=
  functor.mk (λ a, pair (F (pr1 a)) (G (pr2 a)))
             (λ a b f, pair (F (pr1 f)) (G (pr2 f)))
             (λ a, pair_eq !respect_id !respect_id)
             (λ a b c g f, pair_eq !respect_comp !respect_comp)
  end
  end product

  definition precategory_hset [reducible] : precategory hset :=
  precategory.mk (λx y : hset, x → y)
                 _
                 (λx y z g f a, g (f a))
                 (λx a, a)
                 (λx y z w h g f, eq_of_homotopy (λa, idp))
                 (λx y f, eq_of_homotopy (λa, idp))
                 (λx y f, eq_of_homotopy (λa, idp))

  definition Precategory_hset [reducible] : Precategory :=
  Precategory.mk hset precategory_hset

  section
    open iso functor nat_trans
    definition precategory_functor [instance] [reducible] (D C : Precategory)
      : precategory (functor C D) :=
    precategory.mk (λa b, nat_trans a b)
                   (λ a b, @is_hset_nat_trans C D a b)
                   (λ a b c g f, nat_trans.compose g f)
                   (λ a, nat_trans.id)
                   (λ a b c d h g f, !nat_trans.assoc)
                   (λ a b f, !nat_trans.id_left)
                   (λ a b f, !nat_trans.id_right)

    definition Precategory_functor [reducible] (D C : Precategory) : Precategory :=
    precategory.Mk (precategory_functor D C)

  end
  namespace ops
    infixr `^c`:35 := Precategory_functor
  end ops

  section
    open iso functor nat_trans
    /- we prove that if a natural transformation is pointwise an to_fun, then it is an to_fun -/
    variables {C D : Precategory} {F G : C ⇒ D} (η : F ⟹ G) [iso : Π(a : C), is_iso (η a)]
    include iso
    definition nat_trans_inverse : G ⟹ F :=
    nat_trans.mk
      (λc, (η c)⁻¹)
      (λc d f,
      begin
        apply comp_inverse_eq_of_eq_comp,
        apply concat, rotate_left 1, apply assoc,
        apply eq_inverse_comp_of_comp_eq,
        apply inverse,
        apply naturality,
      end)
    definition nat_trans_left_inverse : nat_trans_inverse η ∘n η = nat_trans.id :=
    begin
    fapply (apD011 nat_trans.mk),
      apply eq_of_homotopy, intro c, apply left_inverse,
    apply eq_of_homotopy, intros, apply eq_of_homotopy, intros, apply eq_of_homotopy, intros,
    apply is_hset.elim
    end

    definition nat_trans_right_inverse : η ∘n nat_trans_inverse η = nat_trans.id :=
    begin
    fapply (apD011 nat_trans.mk),
      apply eq_of_homotopy, intro c, apply right_inverse,
    apply eq_of_homotopy, intros, apply eq_of_homotopy, intros, apply eq_of_homotopy, intros,
    apply is_hset.elim
    end

    definition is_iso_nat_trans : is_iso η :=
    is_iso.mk (nat_trans_left_inverse η) (nat_trans_right_inverse η)

    omit iso
    -- local attribute is_iso_nat_trans [instance]
    -- definition functor_iso_functor (H : Π(a : C), F a ≅ G a) : F ≅ G := -- is this true?
    -- iso.mk _
    end

    section
    open iso functor category.ops nat_trans iso.iso
    /- and conversely, if a natural transformation is an iso, it is componentwise an iso -/
    variables {C D : Precategory} {F G : D ^c C} (η : hom F G) [isoη : is_iso η] (c : C)
    include isoη
    definition componentwise_is_iso : is_iso (η c) :=
    @is_iso.mk _ _ _ _ _ (natural_map η⁻¹ c) (ap010 natural_map ( left_inverse η) c)
                                             (ap010 natural_map (right_inverse η) c)

    local attribute componentwise_is_iso [instance]

    definition natural_map_inverse : natural_map η⁻¹ c = (η c)⁻¹ := idp

    definition naturality_iso {c c' : C} (f : c ⟶ c') : G f = η c' ∘ F f ∘ (η c)⁻¹ :=
    calc
      G f = (G f ∘ η c) ∘ (η c)⁻¹ : comp_inverse_cancel_right
      ... = (η c' ∘ F f) ∘ (η c)⁻¹ : {naturality η f}
      ... = η c' ∘ F f ∘ (η c)⁻¹ : assoc

    definition naturality_iso' {c c' : C} (f : c ⟶ c') : (η c')⁻¹ ∘ G f ∘ η c = F f :=
    calc
     (η c')⁻¹ ∘ G f ∘ η c = (η c')⁻¹ ∘ η c' ∘ F f : {naturality η f}
       ... = F f : inverse_comp_cancel_left

    omit isoη

    definition componentwise_iso (η : F ≅ G) (c : C) : F c ≅ G c :=
    @iso.mk _ _ _ _ (natural_map (to_hom η) c)
                    (@componentwise_is_iso _ _ _ _ (to_hom η) (struct η) c)

    definition componentwise_iso_id (c : C) : componentwise_iso (iso.refl F) c = iso.refl (F c) :=
    iso.eq_mk (idpath id)

    definition componentwise_iso_iso_of_eq (p : F = G) (c : C)
      : componentwise_iso (iso_of_eq p) c = iso_of_eq (ap010 to_fun_ob p c) :=
    eq.rec_on p !componentwise_iso_id

    definition natural_map_hom_of_eq (p : F = G) (c : C)
      : natural_map (hom_of_eq p) c = hom_of_eq (ap010 to_fun_ob p c) :=
    eq.rec_on p idp

    definition natural_map_inv_of_eq (p : F = G) (c : C)
      : natural_map (inv_of_eq p) c = hom_of_eq (ap010 to_fun_ob p c)⁻¹ :=
    eq.rec_on p idp

    end

  namespace ops
  infixr `×f`:30 := product.prod_functor
  infixr `ᵒᵖᶠ`:(max+1) := opposite.opposite_functor
  end ops


end category
