-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Floris van Doorn

-- This file contains basic constructions on categories, including common categories


import .basic
import data.unit data.sigma data.prod data.empty data.bool

open eq eq.ops prod
namespace category
  section
  open unit
  definition category_one : category unit :=
  mk (λa b, unit)
     (λ a b c f g, star)
     (λ a, star)
     (λ a b c d f g h, !unit.equal)
     (λ a b f, !unit.equal)
     (λ a b f, !unit.equal)
  end

  section
  variables {ob : Type} {C : category ob} {a b c : ob}
  definition opposite (C : category ob) : category ob :=
  mk (λa b, hom b a)
     (λ a b c f g, g ∘ f)
     (λ a, id)
     (λ a b c d f g h, symm !assoc)
     (λ a b f, !id_right)
     (λ a b f, !id_left)
  --definition compose_opposite {C : category ob} {a b c : ob} {g : a => b} {f : b => c} : compose
  precedence `∘op` : 60
  infixr `∘op` := @compose _ (opposite _) _ _ _

  theorem compose_op {f : @hom ob C a b} {g : hom b c} : f ∘op g = g ∘ f :=
  rfl

  theorem op_op {C : category ob} : opposite (opposite C) = C :=
  category.rec (λ hom comp id assoc idl idr, refl (mk _ _ _ _ _ _)) C
  end

  definition Opposite (C : Category) : Category :=
  Category.mk (objects C) (opposite (category_instance C))

  section
  definition type_category : category Type :=
  mk (λa b, a → b)
     (λ a b c, function.compose)
     (λ a, function.id)
     (λ a b c d h g f, symm (function.compose_assoc h g f))
     (λ a b f, function.compose_id_left f)
     (λ a b f, function.compose_id_right f)
  end

  section
  open decidable unit empty
  parameters (A : Type) {H : decidable_eq A}
  private definition set_hom (a b : A) := decidable.rec_on (H a b) (λh, unit) (λh, empty)
  private theorem set_hom_subsingleton [instance] (a b : A) : subsingleton (set_hom a b) := _
  private definition set_compose {a b c : A} (g : set_hom b c) (f : set_hom a b) : set_hom a c :=
  decidable.rec_on
    (H b c)
    (λ Hbc g, decidable.rec_on
      (H a b)
      (λ Hab f, rec_on_true (trans Hab Hbc) ⋆)
      (λh f, empty.rec _ f) f)
    (λh (g : empty), empty.rec _ g) g

  definition set_category : category A :=
  mk (λa b, set_hom a b)
     (λ a b c g f, set_compose g f)
     (λ a, rec_on_true rfl ⋆)
     (λ a b c d h g f, subsingleton.elim _ _ _)
     (λ a b f, subsingleton.elim _ _ _)
     (λ a b f, subsingleton.elim _ _ _)
  end

  section
  open bool
  definition category_two := set_category bool
  end


  section cat_of_cat
  definition category_of_categories : category Category :=
  mk (λ a b, Functor a b)
     (λ a b c g f, functor.Compose g f)
     (λ a, functor.Id)
     (λ a b c d h g f, !functor.Assoc)
     (λ a b f, !functor.Id_left)
     (λ a b f, !functor.Id_right)
  end cat_of_cat

  section product
  open prod
  definition product_category {obC obD : Type} (C : category obC) (D : category obD)
      : category (obC × obD) :=
  mk (λa b, hom (pr1 a) (pr1 b) × hom (pr2 a) (pr2 b))
     (λ a b c g f, (pr1 g ∘ pr1 f , pr2 g ∘ pr2 f) )
     (λ a, (id,id))
     (λ a b c d h g f, pair_eq    !assoc    !assoc   )
     (λ a b f,         prod.equal !id_left  !id_left )
     (λ a b f,         prod.equal !id_right !id_right)

  end product

namespace ops
  notation `Cat` := category_of_categories
  notation `type` := type_category
  notation 1 := category_one
  postfix `ᵒᵖ`:max := opposite
  infixr `×` := product_category
  instance category_of_categories type_category category_one product_category
end ops

  section functor_category
  parameters {obC obD : Type} (C : category obC) (D : category obD)
  definition functor_category : category (functor C D) :=
  mk (λa b, natural_transformation a b)
     (λ a b c g f, natural_transformation.compose g f)
     (λ a, natural_transformation.id)
     (λ a b c d h g f, !natural_transformation.assoc)
     (λ a b f, !natural_transformation.id_left)
     (λ a b f, !natural_transformation.id_right)
  end functor_category

  section
  open sigma

  definition slice_category [reducible] {ob : Type} (C : category ob) (c : ob) : category (Σ(b : ob), hom b c) :=
  mk (λa b, Σ(g : hom (dpr1 a) (dpr1 b)), dpr2 b ∘ g = dpr2 a)
     (λ a b c g f, dpair (dpr1 g ∘ dpr1 f)
       (show dpr2 c ∘ (dpr1 g ∘ dpr1 f) = dpr2 a,
	 proof
	 calc
	   dpr2 c ∘ (dpr1 g ∘ dpr1 f) = (dpr2 c ∘ dpr1 g) ∘ dpr1 f : !assoc
	     ... = dpr2 b ∘ dpr1 f : {dpr2 g}
	     ... = dpr2 a : {dpr2 f}
	 qed))
     (λ a, dpair id !id_right)
     (λ a b c d h g f, dpair_eq    !assoc    !proof_irrel)
     (λ a b f,         sigma.equal !id_left  !proof_irrel)
     (λ a b f,         sigma.equal !id_right !proof_irrel)
  -- We use !proof_irrel instead of rfl, to give the unifier an easier time
  end --remove
  namespace slice
  section --remove
  open sigma category.ops --remove sigma
  instance slice_category
  parameters {ob : Type} (C : category ob)
  definition forgetful (x : ob) : (slice_category C x) ⇒ C :=
  functor.mk (λ a, dpr1 a)
	     (λ a b f, dpr1 f)
	     (λ a, rfl)
	     (λ a b c g f, rfl)
  definition composition_functor {x y : ob} (h : x ⟶ y) : slice_category C x ⇒ slice_category C y :=
  functor.mk (λ a, dpair (dpr1 a) (h ∘ dpr2 a))
	     (λ a b f, dpair (dpr1 f)
	       (calc
		 (h ∘ dpr2 b) ∘ dpr1 f = h ∘ (dpr2 b ∘ dpr1 f) : !assoc⁻¹
		    ... = h ∘ dpr2 a : {dpr2 f}))
	     (λ a, rfl)
	     (λ a b c g f, dpair_eq rfl !proof_irrel)
  -- the following definition becomes complicated
  -- definition slice_functor : C ⇒ category_of_categories :=
  -- functor.mk (λ a, Category.mk _ (slice_category C a))
  --            (λ a b f, Functor.mk (composition_functor f))
  --            (λ a, congr_arg Functor.mk
  --              (congr_arg4_dep functor.mk
  --		 (funext (λx, sigma.equal rfl !id_left))
  --		 sorry
  --		 !proof_irrel
  --		 !proof_irrel))
  --            (λ a b c g f, sorry)
  end
  end slice

  section coslice
  open sigma

  definition coslice {ob : Type} (C : category ob) (c : ob) : category (Σ(b : ob), hom c b) :=
  mk (λa b, Σ(g : hom (dpr1 a) (dpr1 b)), g ∘ dpr2 a = dpr2 b)
     (λ a b c g f, dpair (dpr1 g ∘ dpr1 f)
       (show (dpr1 g ∘ dpr1 f) ∘ dpr2 a = dpr2 c,
	 proof
	 calc
	   (dpr1 g ∘ dpr1 f) ∘ dpr2 a = dpr1 g ∘ (dpr1 f ∘ dpr2 a): symm !assoc
	     ... = dpr1 g ∘ dpr2 b : {dpr2 f}
	     ... = dpr2 c : {dpr2 g}
	 qed))
     (λ a, dpair id !id_left)
     (λ a b c d h g f, dpair_eq    !assoc    !proof_irrel)
     (λ a b f,         sigma.equal !id_left  !proof_irrel)
     (λ a b f,         sigma.equal !id_right !proof_irrel)

  -- theorem slice_coslice_opp {ob : Type} (C : category ob) (c : ob) :
  --     coslice C c = opposite (slice (opposite C) c) :=
  -- sorry
  end coslice

  section arrow
  open sigma eq.ops
  -- theorem concat_commutative_squares {ob : Type} {C : category ob} {a1 a2 a3 b1 b2 b3 : ob}
  --     {f1 : a1 => b1} {f2 : a2 => b2} {f3 : a3 => b3} {g2 : a2 => a3} {g1 : a1 => a2}
  --     {h2 : b2 => b3} {h1 : b1 => b2} (H1 : f2 ∘ g1 = h1 ∘ f1) (H2 : f3 ∘ g2 = h2 ∘ f2)
  --       : f3 ∘ (g2 ∘ g1) = (h2 ∘ h1) ∘ f1 :=
  -- calc
  --   f3 ∘ (g2 ∘ g1) = (f3 ∘ g2) ∘ g1 : assoc
  --     ... = (h2 ∘ f2) ∘ g1 : {H2}
  --     ... = h2 ∘ (f2 ∘ g1) : symm assoc
  --     ... = h2 ∘ (h1 ∘ f1) : {H1}
  --     ... = (h2 ∘ h1) ∘ f1 : assoc

  -- definition arrow {ob : Type} (C : category ob) : category (Σ(a b : ob), hom a b) :=
  -- mk (λa b, Σ(g : hom (dpr1 a) (dpr1 b)) (h : hom (dpr2' a) (dpr2' b)),
  --      dpr3 b ∘ g = h ∘ dpr3 a)
  --    (λ a b c g f, dpair (dpr1 g ∘ dpr1 f) (dpair (dpr2' g ∘ dpr2' f) (concat_commutative_squares (dpr3 f) (dpr3 g))))
  --    (λ a, dpair id (dpair id (id_right ⬝ (symm id_left))))
  --    (λ a b c d h g f, dtrip_eq2   assoc    assoc    !proof_irrel)
  --    (λ a b f,         trip.equal2 id_left  id_left  !proof_irrel)
  --    (λ a b f,         trip.equal2 id_right id_right !proof_irrel)

  -- make these definitions private?
  variables {ob : Type} {C : category ob}
  protected definition arrow_obs (ob : Type) (C : category ob) := Σ(a b : ob), hom a b
  variables {a b : arrow_obs ob C}
  protected definition src    (a : arrow_obs ob C) : ob                  := dpr1 a
  protected definition dst    (a : arrow_obs ob C) : ob                  := dpr2' a
  protected definition to_hom (a : arrow_obs ob C) : hom (src a) (dst a) := dpr3 a

  protected definition arrow_hom (a b : arrow_obs ob C) : Type :=
  Σ (g : hom (src a) (src b)) (h : hom (dst a) (dst b)), to_hom b ∘ g = h ∘ to_hom a

  protected definition hom_src (m : arrow_hom a b) : hom (src a) (src b) := dpr1 m
  protected definition hom_dst (m : arrow_hom a b) : hom (dst a) (dst b) := dpr2' m
  protected definition commute (m : arrow_hom a b) : to_hom b ∘ (hom_src m) = (hom_dst m) ∘ to_hom a
  := dpr3 m

  definition arrow (ob : Type) (C : category ob) : category (arrow_obs ob C) :=
  mk (λa b, arrow_hom a b)
     (λ a b c g f, dpair (hom_src g ∘ hom_src f) (dpair (hom_dst g ∘ hom_dst f)
	(show to_hom c ∘ (hom_src g ∘ hom_src f) = (hom_dst g ∘ hom_dst f) ∘ to_hom a,
	 proof
	 calc
	 to_hom c ∘ (hom_src g ∘ hom_src f) = (to_hom c ∘ hom_src g) ∘ hom_src f : !assoc
	   ... = (hom_dst g ∘ to_hom b) ∘ hom_src f  : {commute g}
	   ... = hom_dst g ∘ (to_hom b ∘ hom_src f)  : symm !assoc
	   ... = hom_dst g ∘ (hom_dst f ∘ to_hom a)  : {commute f}
	   ... = (hom_dst g ∘ hom_dst f) ∘ to_hom a  : !assoc
	 qed)
       ))
     (λ a, dpair id (dpair id (!id_right ⬝ (symm !id_left))))
     (λ a b c d h g f, dtrip_eq_ndep   !assoc    !assoc    !proof_irrel)
     (λ a b f,         trip.equal_ndep !id_left  !id_left  !proof_irrel)
     (λ a b f,         trip.equal_ndep !id_right !id_right !proof_irrel)

  end arrow

end category

  -- definition foo
  --     : category (sorry) :=
  -- mk (λa b, sorry)
  --    (λ a b c g f, sorry)
  --    (λ a, sorry)
  --    (λ a b c d h g f, sorry)
  --    (λ a b f, sorry)
  --    (λ a b f, sorry)
