/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Definition of functors involving at least two different constructions of categories
-/

import ..constructions.functor ..constructions.product ..constructions.opposite
       ..constructions.set

open category nat_trans eq prod prod.ops

namespace functor

  section
  open iso equiv
  variables {C D E : Precategory} (F F' : C ×c D ⇒ E) (G G' : C ⇒ E ^c D)
  /- currying a functor -/
  definition functor_curry_ob [reducible] [constructor] (c : C) : D ⇒ E :=
  F ∘f (constant_functor D c ×f 1)

  definition functor_curry_hom [constructor] ⦃c c' : C⦄ (f : c ⟶ c')
    : functor_curry_ob F c ⟹ functor_curry_ob F c' :=
  F ∘fn (constant_nat_trans D f ×n 1)

  local abbreviation Fhom [constructor] := @functor_curry_hom

  theorem functor_curry_id (c : C) : Fhom F (ID c) = nat_trans.id :=
  nat_trans_eq (λd, respect_id F _)

  theorem functor_curry_comp ⦃c c' c'' : C⦄ (f' : c' ⟶ c'') (f : c ⟶ c')
    : Fhom F (f' ∘ f) = Fhom F f' ∘n Fhom F f :=
  begin
    apply @nat_trans_eq,
    intro d, calc
    natural_map (Fhom F (f' ∘ f)) d = F (f' ∘ f, id) : by esimp
      ... = F (f' ∘ f, id ∘ id)                      : by rewrite id_id
      ... = F ((f',id) ∘ (f, id))                    : by esimp
      ... = F (f',id) ∘ F (f, id)                    : by rewrite [respect_comp F]
      ... = natural_map ((Fhom F f') ∘ (Fhom F f)) d : by esimp
  end

  definition functor_curry [reducible] [constructor] : C ⇒ E ^c D :=
  functor.mk (functor_curry_ob F)
             (functor_curry_hom F)
             (functor_curry_id F)
             (functor_curry_comp F)

  /- uncurrying a functor -/

  definition functor_uncurry_ob [reducible] (p : C ×c D) : E :=
  to_fun_ob (G p.1) p.2

  definition functor_uncurry_hom ⦃p p' : C ×c D⦄ (f : hom p p')
    : functor_uncurry_ob G p ⟶ functor_uncurry_ob G p'  :=
  to_fun_hom (to_fun_ob G p'.1) f.2 ∘ natural_map (to_fun_hom G f.1) p.2
  local abbreviation Ghom := @functor_uncurry_hom

  theorem functor_uncurry_id (p : C ×c D) : Ghom G (ID p) = id :=
  calc
    Ghom G (ID p) = to_fun_hom (to_fun_ob G p.1) id ∘ natural_map (to_fun_hom G id) p.2 : by esimp
      ... = id ∘ natural_map (to_fun_hom G id) p.2 : by rewrite respect_id
      ... = id ∘ natural_map nat_trans.id p.2      : by rewrite respect_id
      ... = id                                     : id_id

  theorem functor_uncurry_comp ⦃p p' p'' : C ×c D⦄ (f' : p' ⟶ p'') (f : p ⟶ p')
    : Ghom G (f' ∘ f) = Ghom G f' ∘ Ghom G f :=
  calc
    Ghom G (f' ∘ f)
          = to_fun_hom (to_fun_ob G p''.1) (f'.2 ∘ f.2) ∘ natural_map (to_fun_hom G (f'.1 ∘ f.1)) p.2 : by esimp
      ... = (to_fun_hom (to_fun_ob G p''.1) f'.2 ∘ to_fun_hom (to_fun_ob G p''.1) f.2)
              ∘ natural_map (to_fun_hom G (f'.1 ∘ f.1)) p.2                : by rewrite respect_comp
      ... = (to_fun_hom (to_fun_ob G p''.1) f'.2 ∘ to_fun_hom (to_fun_ob G p''.1) f.2)
              ∘ natural_map (to_fun_hom G f'.1 ∘ to_fun_hom G f.1) p.2     : by rewrite respect_comp
      ... = (to_fun_hom (to_fun_ob G p''.1) f'.2 ∘ to_fun_hom (to_fun_ob G p''.1) f.2)
             ∘ (natural_map (to_fun_hom G f'.1) p.2 ∘ natural_map (to_fun_hom G f.1) p.2) : by esimp
      ... = (to_fun_hom (to_fun_ob G p''.1) f'.2 ∘ natural_map (to_fun_hom G f'.1) p'.2)
              ∘ (to_fun_hom (to_fun_ob G p'.1) f.2 ∘ natural_map (to_fun_hom G f.1) p.2) :
                  by rewrite [square_prepostcompose (!naturality⁻¹ᵖ) _ _]
      ... = Ghom G f' ∘ Ghom G f : by esimp

  definition functor_uncurry [reducible] [constructor] : C ×c D ⇒ E :=
  functor.mk (functor_uncurry_ob G)
             (functor_uncurry_hom G)
             (functor_uncurry_id G)
             (functor_uncurry_comp G)

  theorem functor_uncurry_functor_curry : functor_uncurry (functor_curry F) = F :=
  functor_eq (λp, ap (to_fun_ob F) !prod.eta)
  begin
    intro cd cd' fg,
    cases cd with c d, cases cd' with c' d', cases fg with f g,
    transitivity to_fun_hom (functor_uncurry (functor_curry F)) (f, g),
    apply id_leftright,
    show (functor_uncurry (functor_curry F)) (f, g) = F (f,g),
      from calc
        (functor_uncurry (functor_curry F)) (f, g) = to_fun_hom F (id, g) ∘ to_fun_hom F (f, id) : by esimp
          ... = F (id ∘ f, g ∘ id) : by krewrite [-respect_comp F (id,g) (f,id)]
          ... = F (f, g ∘ id)      : by rewrite id_left
          ... = F (f,g)            : by rewrite id_right,
  end

  definition functor_curry_functor_uncurry_ob (c : C)
    : functor_curry (functor_uncurry G) c = G c :=
  begin
    fapply functor_eq,
     { intro d, reflexivity},
     { intro d d' g, refine !id_leftright ⬝ _, esimp,
       rewrite [▸*, ↑functor_uncurry_hom, respect_id, ▸*, id_right]}
  end

  theorem functor_curry_functor_uncurry : functor_curry (functor_uncurry G) = G :=
  begin
    fapply functor_eq, exact (functor_curry_functor_uncurry_ob G),
    intro c c' f,
    fapply nat_trans_eq,
    intro d,
    apply concat,
      {apply (ap (λx, x ∘ _)),
        apply concat, apply natural_map_hom_of_eq, apply (ap hom_of_eq), apply ap010_functor_eq},
    apply concat,
       {apply (ap (λx, _ ∘ x)), apply (ap (λx, _ ∘ x)),
         apply concat, apply natural_map_inv_of_eq,
         apply (ap (λx, hom_of_eq x⁻¹)), apply ap010_functor_eq},
    apply concat, apply id_leftright,
    apply concat, apply (ap (λx, x ∘ _)), apply respect_id,
    apply id_left
  end

  /-
     This only states that the carriers of (C ^ D) ^ E and C ^ (E × D) are equivalent.
     In [exponential laws] we prove that these are in fact isomorphic categories
  -/
  definition prod_functor_equiv_functor_functor [constructor] (C D E : Precategory)
    : (C ×c D ⇒ E) ≃ (C ⇒ E ^c D) :=
  equiv.MK functor_curry
           functor_uncurry
           functor_curry_functor_uncurry
           functor_uncurry_functor_curry

  variables {F F' G G'}
  definition nat_trans_curry_nat [constructor] (η : F ⟹ F') (c : C)
    : functor_curry_ob F c ⟹ functor_curry_ob F' c :=
  begin
    fapply nat_trans.mk: esimp,
    { intro d, exact η (c, d)},
    { intro d d' f, apply naturality}
  end

  definition nat_trans_curry [constructor] (η : F ⟹ F')
    : functor_curry F ⟹ functor_curry F' :=
  begin
    fapply nat_trans.mk: esimp,
    { exact nat_trans_curry_nat η},
    { intro c c' f, apply nat_trans_eq, intro d, esimp, apply naturality}
  end

  definition nat_trans_uncurry [constructor] (η : G ⟹ G')
    : functor_uncurry G ⟹ functor_uncurry G' :=
  begin
    fapply nat_trans.mk: esimp,
    { intro v, unfold functor_uncurry_ob, exact (η v.1) v.2},
    { intro v w f, unfold functor_uncurry_hom,
      rewrite [-assoc, ap010 natural_map (naturality η f.1) v.2, assoc, naturality, -assoc]}
  end
  end

  section
  open is_trunc

  /- hom-functors -/

  definition hom_functor_assoc {C : Precategory} {a1 a2 a3 a4 a5 a6 : C}
    (f1 : hom a5 a6) (f2 : hom a4 a5) (f3 : hom a3 a4) (f4 : hom a2 a3) (f5 : hom a1 a2)
      : (f1 ∘ f2) ∘ f3 ∘ (f4 ∘ f5) = f1 ∘ (f2 ∘ f3 ∘ f4) ∘ f5 :=
  calc
        _ = f1 ∘ f2 ∘ f3 ∘ f4 ∘ f5     : by rewrite -assoc
      ... = f1 ∘ (f2 ∘ f3) ∘ f4 ∘ f5   : by rewrite -assoc
      ... = f1 ∘ ((f2 ∘ f3) ∘ f4) ∘ f5 : by rewrite -(assoc (f2 ∘ f3) _ _)
      ... = _                          : by rewrite (assoc f2 f3 f4)

  -- the functor hom(-,-)
  definition hom_functor.{u v} [constructor] (C : Precategory.{u v}) : Cᵒᵖ ×c C ⇒ set.{v} :=
  functor.mk
    (λ (x : Cᵒᵖ ×c C), @homset (Cᵒᵖ) C x.1 x.2)
    (λ (x y : Cᵒᵖ ×c C) (f : @category.precategory.hom (Cᵒᵖ ×c C) (Cᵒᵖ ×c C) x y)
       (h : @homset (Cᵒᵖ) C x.1 x.2), f.2 ∘[C] (h ∘[C] f.1))
    (λ x, abstract @eq_of_homotopy _ _ _ (ID (@homset Cᵒᵖ C x.1 x.2))
            (λ h, concat (by apply @id_left) (by apply @id_right)) end)
    (λ x y z g f, abstract eq_of_homotopy (by intros; apply @hom_functor_assoc) end)

  -- the functor hom(-, c)
  definition hom_functor_left.{u v} [constructor] (C : Precategory.{u v}) (c : C)
    : Cᵒᵖ ⇒ set.{v} :=
  hom_functor C ∘f (1 ×f constant_functor Cᵒᵖ c)

  -- the functor hom(c, -)
  definition hom_functor_right.{u v} [constructor] (C : Precategory.{u v}) (c : C)
    : C ⇒ set.{v} :=
  hom_functor C ∘f (constant_functor C c ×f 1)


  end



end functor
