/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.precategory.yoneda
Author: Floris van Doorn
-/

--note: modify definition in category.set
import algebra.category.constructions .morphism

open category eq category.ops functor prod.ops is_trunc

set_option pp.beta true
namespace yoneda
  set_option class.conservative false

  --TODO: why does this take so much steps? (giving more information than "assoc" hardly helps)
  definition representable_functor_assoc [C : Precategory] {a1 a2 a3 a4 a5 a6 : C}
    (f1 : hom a5 a6) (f2 : hom a4 a5) (f3 : hom a3 a4) (f4 : hom a2 a3) (f5 : hom a1 a2)
      : (f1 ∘ f2) ∘ f3 ∘ (f4 ∘ f5) = f1 ∘ (f2 ∘ f3 ∘ f4) ∘ f5 :=
  calc
        _ = f1 ∘ f2 ∘ f3 ∘ f4 ∘ f5 : assoc
      ... = f1 ∘ (f2 ∘ f3) ∘ f4 ∘ f5 : assoc
      ... = f1 ∘ ((f2 ∘ f3) ∘ f4) ∘ f5 : assoc
      ... = _ : assoc

  --disturbing behaviour: giving the type of f "(x ⟶ y)" explicitly makes the unifier loop
  definition representable_functor (C : Precategory) : Cᵒᵖ ×c C ⇒ set :=
  functor.mk (λ(x : Cᵒᵖ ×c C), homset x.1 x.2)
             (λ(x y : Cᵒᵖ ×c C) (f : _) (h : homset x.1 x.2), f.2 ∘⁅ C ⁆ (h ∘⁅ C ⁆ f.1))
             proof (λ(x : Cᵒᵖ ×c C), eq_of_homotopy (λ(h : homset x.1 x.2), !id_left ⬝ !id_right)) qed
             -- (λ(x y z : Cᵒᵖ ×c C) (g : y ⟶ z) (f : x ⟶ y), eq_of_homotopy (λ(h : hom x.1 x.2), representable_functor_assoc g.2 f.2 h f.1 g.1))
             begin
               intros (x, y, z, g, f), apply eq_of_homotopy, intro h,
               exact (representable_functor_assoc g.2 f.2 h f.1 g.1),
             end
end yoneda


open is_equiv equiv

namespace functor
  open prod nat_trans
  variables {C D E : Precategory}

  definition functor_curry_ob (F : C ×c D ⇒ E) (c : C) : E ^c D :=
  functor.mk (λd, F (c,d))
             (λd d' g, F (id, g))
             (λd, !respect_id)
             (λd₁ d₂ d₃ g' g, proof calc
               F (id, g' ∘ g) = F (id ∘ id, g' ∘ g) : {(id_compose c)⁻¹}
                 ... = F ((id,g') ∘ (id, g)) : idp
                 ... = F (id,g') ∘ F (id, g) : respect_comp F qed)

  local abbreviation Fob := @functor_curry_ob
  definition functor_curry_mor (F : C ×c D ⇒ E) ⦃c c' : C⦄ (f : c ⟶ c') : Fob F c ⟹ Fob F c'  :=
  nat_trans.mk (λd, F (f, id))
               (λd d' g, proof calc
                 F (id, g) ∘ F (f, id) = F (id ∘ f, g ∘ id) : respect_comp F
                   ... = F (f, g ∘ id) : {id_left f}
                   ... = F (f, g) : {id_right g}
                   ... = F (f ∘ id, g) : {(id_right f)⁻¹}
                   ... = F (f ∘ id, id ∘ g) : {(id_left g)⁻¹}
                   ... = F (f, id) ∘ F (id, g) :  (respect_comp F (f, id) (id, g))⁻¹ᵖ
            qed)

  local abbreviation Fmor := @functor_curry_mor
  definition functor_curry_mor_def (F : C ×c D ⇒ E) ⦃c c' : C⦄ (f : c ⟶ c') (d : D) :
    (Fmor F f) d = F (f, id) := idp

  definition functor_curry_id (F : C ×c D ⇒ E) (c : C) : Fmor F (ID c) = nat_trans.id :=
  nat_trans_eq_mk (λd, respect_id F _)

  definition functor_curry_comp (F : C ×c D ⇒ E) ⦃c c' c'' : C⦄ (f' : c' ⟶ c'') (f : c ⟶ c')
    : Fmor F (f' ∘ f) = Fmor F f' ∘n Fmor F f :=
  nat_trans_eq_mk (λd, calc
                    natural_map (Fmor F (f' ∘ f)) d = F (f' ∘ f, id) : functor_curry_mor_def
                      ... = F (f' ∘ f, id ∘ id) : {(id_compose d)⁻¹}
                      ... = F ((f',id) ∘ (f, id)) : idp
                      ... = F (f',id) ∘ F (f, id) : respect_comp F
                      ... = natural_map ((Fmor F f') ∘ (Fmor F f)) d : idp)

--respect_comp F (g, id) (f, id)
  definition functor_curry (F : C ×c D ⇒ E) : C ⇒ E ^c D :=
  functor.mk (functor_curry_ob F)
             (functor_curry_mor F)
             (functor_curry_id F)
             (functor_curry_comp F)


  definition is_equiv_functor_curry : is_equiv (@functor_curry C D E) := sorry

  definition equiv_functor_curry : (C ×c D ⇒ E) ≃ (C ⇒ E ^c D) :=
  equiv.mk _ !is_equiv_functor_curry
end functor
-- Coq uses unit/counit definitions as basic

-- open yoneda precategory.product precategory.opposite functor morphism
--   --universe levels are given explicitly because Lean uses 6 variables otherwise

--   structure adjoint.{u v} [C D : Precategory.{u v}] (F : C ⇒ D) (G : D ⇒ C) : Type.{max u v} :=
--   (nat_iso : (representable_functor D) ∘f (prod_functor (opposite_functor F) (functor.ID D)) ⟹
--              (representable_functor C) ∘f (prod_functor (functor.ID (Cᵒᵖ)) G))
--   (is_iso_nat_iso : is_iso nat_iso)

--   infix `⊣`:55 := adjoint

-- namespace adjoint
--   universe variables l1 l2
--   variables [C D : Precategory.{l1 l2}] (F : C ⇒ D) (G : D ⇒ C)



-- end adjoint
