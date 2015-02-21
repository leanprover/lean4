-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Floris van Doorn, Jakob von Raumer

-- This file contains basic constructions on precategories, including common precategories


import .nat_trans
import types.prod types.sigma types.pi

open eq prod eq eq.ops equiv is_trunc funext

namespace precategory
  namespace opposite

  definition opposite [reducible] {ob : Type} (C : precategory ob) : precategory ob :=
  mk (λ a b, hom b a)
     (λ b a, !homH)
     (λ a b c f g, g ∘ f)
     (λ a, id)
     (λ a b c d f g h, !assoc⁻¹)
     (λ a b f, !id_right)
     (λ a b f, !id_left)

  definition Opposite [reducible] (C : Precategory) : Precategory := Mk (opposite C)

  infixr `∘op`:60 := @compose _ (opposite _) _ _ _

  variables {C : Precategory} {a b c : C}

  set_option apply.class_instance false -- disable class instance resolution in the apply tactic

  theorem compose_op {f : hom a b} {g : hom b c} : f ∘op g = g ∘ f := idp

  -- TODO: Decide whether just to use funext for this theorem or
  --       take the trick they use in Coq-HoTT, and introduce a further
  --       axiom in the definition of precategories that provides thee
  --       symmetric associativity proof.
  definition op_op' {ob : Type} (C : precategory ob) : opposite (opposite C) = C :=
  begin
    apply (precategory.rec_on C), intros (hom', homH', comp', ID', assoc', id_left', id_right'),
    apply (ap (λassoc'', precategory.mk hom' @homH' comp' ID' assoc'' id_left' id_right')),
    repeat ( apply funext.eq_of_homotopy ; intros ),
    apply ap,
    apply (@is_hset.elim), apply !homH',
  end

  definition op_op : Opposite (Opposite C) = C :=
  (ap (Precategory.mk C) (op_op' C)) ⬝ !Precategory.eta

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

  definition prod_precategory [reducible] [instance] {obC obD : Type} (C : precategory obC) (D : precategory obD)
      : precategory (obC × obD) :=
  mk (λ a b, hom (pr1 a) (pr1 b) × hom (pr2 a) (pr2 b))
     (λ a b, !is_trunc_prod)
     (λ a b c g f, (pr1 g ∘ pr1 f , pr2 g ∘ pr2 f) )
     (λ a, (id, id))
     (λ a b c d h g f, pair_eq  !assoc    !assoc   )
     (λ a b f,         prod_eq  !id_left  !id_left )
     (λ a b f,         prod_eq  !id_right !id_right)

  definition Prod_precategory [reducible] (C D : Precategory) : Precategory := Mk (prod_precategory C D)

  end
  end product

  namespace ops
    --notation 1 := Category_one
    --notation 2 := Category_two
    postfix `ᵒᵖ`:max := opposite.Opposite
    infixr `×c`:30 := product.Prod_precategory
    --instance [persistent] type_category category_one
    --                      category_two product.prod_category
    attribute product.prod_precategory [instance]

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

  namespace ops
  infixr `×f`:30 := product.prod_functor
  infixr `ᵒᵖᶠ`:max := opposite.opposite_functor
  abbreviation set := Precategory_hset
  end ops

  section precategory_functor
  variables (C D : Precategory)
  definition precategory_functor [reducible] : precategory (functor C D) :=
  mk (λa b, nat_trans a b)
     (λ a b, @nat_trans.to_hset C D a b)
     (λ a b c g f, nat_trans.compose g f)
     (λ a, nat_trans.id)
     (λ a b c d h g f, !nat_trans.assoc)
     (λ a b f, !nat_trans.id_left)
     (λ a b f, !nat_trans.id_right)
  end precategory_functor

end precategory
