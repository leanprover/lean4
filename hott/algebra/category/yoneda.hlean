/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.category.yoneda
Authors: Floris van Doorn
-/

--note: modify definition in category.set
import .constructions.functor .constructions.hset .constructions.product .constructions.opposite

open category eq category.ops functor prod.ops is_trunc iso

namespace yoneda
  set_option class.conservative false

  definition representable_functor_assoc [C : Precategory] {a1 a2 a3 a4 a5 a6 : C}
    (f1 : hom a5 a6) (f2 : hom a4 a5) (f3 : hom a3 a4) (f4 : hom a2 a3) (f5 : hom a1 a2)
      : (f1 ∘ f2) ∘ f3 ∘ (f4 ∘ f5) = f1 ∘ (f2 ∘ f3 ∘ f4) ∘ f5 :=
  calc
        _ = f1 ∘ f2 ∘ f3 ∘ f4 ∘ f5     : by rewrite -assoc
      ... = f1 ∘ (f2 ∘ f3) ∘ f4 ∘ f5   : by rewrite -assoc
      ... = f1 ∘ ((f2 ∘ f3) ∘ f4) ∘ f5 : by rewrite -(assoc (f2 ∘ f3) _ _)
      ... = _                          : by rewrite (assoc f2 f3 f4)

  definition hom_functor (C : Precategory) : Cᵒᵖ ×c C ⇒ set :=
  functor.mk (λ(x : Cᵒᵖ ×c C), homset x.1 x.2)
             (λ(x y : Cᵒᵖ ×c C) (f : _) (h : homset x.1 x.2), f.2 ∘⁅ C ⁆ (h ∘⁅ C ⁆ f.1))
             begin
               intro x, apply eq_of_homotopy, intro h, exact (!id_left ⬝ !id_right)
             end
             begin
               intros [x, y, z, g, f], apply eq_of_homotopy, intro h,
               exact (representable_functor_assoc g.2 f.2 h f.1 g.1),
             end
end yoneda


open is_equiv equiv

namespace functor
  open prod nat_trans
  variables {C D E : Precategory} (F : C ×c D ⇒ E) (G : C ⇒ E ^c D)
  definition functor_curry_ob [reducible] (c : C) : E ^c D :=
  functor.mk (λd, F (c,d))
             (λd d' g, F (id, g))
             (λd, !respect_id)
             (λd₁ d₂ d₃ g' g, calc
               F (id, g' ∘ g) = F (id ∘ id, g' ∘ g) : by rewrite id_comp
                 ... = F ((id,g') ∘ (id, g))        : by esimp
                 ... = F (id,g') ∘ F (id, g)        : by rewrite respect_comp)

  local abbreviation Fob := @functor_curry_ob

  definition functor_curry_hom ⦃c c' : C⦄ (f : c ⟶ c') : Fob F c ⟹ Fob F c' :=
  nat_trans.mk (λd, F (f, id))
               (λd d' g, calc
                 F (id, g) ∘ F (f, id) = F (id ∘ f, g ∘ id) : respect_comp F
                   ... = F (f, g ∘ id)         : by rewrite id_left
                   ... = F (f, g)              : by rewrite id_right
                   ... = F (f ∘ id, g)         : by rewrite id_right
                   ... = F (f ∘ id, id ∘ g)    : by rewrite id_left
                   ... = F (f, id) ∘ F (id, g) :  (respect_comp F (f, id) (id, g))⁻¹ᵖ)

  local abbreviation Fhom := @functor_curry_hom

  theorem functor_curry_hom_def ⦃c c' : C⦄ (f : c ⟶ c') (d : D) :
    (Fhom F f) d = to_fun_hom F (f, id) := idp

  theorem functor_curry_id (c : C) : Fhom F (ID c) = nat_trans.id :=
  nat_trans_eq_mk (λd, respect_id F _)

  theorem functor_curry_comp ⦃c c' c'' : C⦄ (f' : c' ⟶ c'') (f : c ⟶ c')
    : Fhom F (f' ∘ f) = Fhom F f' ∘n Fhom F f :=
  nat_trans_eq_mk (λd, calc
    natural_map (Fhom F (f' ∘ f)) d = F (f' ∘ f, id) : functor_curry_hom_def
      ... = F (f' ∘ f, id ∘ id)                      : by rewrite id_comp
      ... = F ((f',id) ∘ (f, id))                    : by esimp
      ... = F (f',id) ∘ F (f, id)                    : respect_comp F
      ... = natural_map ((Fhom F f') ∘ (Fhom F f)) d : by esimp)

  definition functor_curry [reducible] : C ⇒ E ^c D :=
  functor.mk (functor_curry_ob F)
             (functor_curry_hom F)
             (functor_curry_id F)
             (functor_curry_comp F)

  definition functor_uncurry_ob [reducible] (p : C ×c D) : E :=
  to_fun_ob (G p.1) p.2
  local abbreviation Gob := @functor_uncurry_ob

  definition functor_uncurry_hom ⦃p p' : C ×c D⦄ (f : hom p p') : Gob G p ⟶ Gob G p'  :=
  to_fun_hom (to_fun_ob G p'.1) f.2 ∘ natural_map (to_fun_hom G f.1) p.2
  local abbreviation Ghom := @functor_uncurry_hom

  theorem functor_uncurry_id (p : C ×c D) : Ghom G (ID p) = id :=
  calc
    Ghom G (ID p) = to_fun_hom (to_fun_ob G p.1) id ∘ natural_map (to_fun_hom G id) p.2 : by esimp
      ... = id ∘ natural_map (to_fun_hom G id) p.2 : by rewrite respect_id
      ... = id ∘ natural_map nat_trans.id p.2      : by rewrite respect_id
      ... = id                                     : id_comp

  theorem functor_uncurry_comp ⦃p p' p'' : C ×c D⦄ (f' : p' ⟶ p'') (f : p ⟶ p')
    : Ghom G (f' ∘ f) = Ghom G f' ∘ Ghom G f :=
  calc
    Ghom G (f' ∘ f)
          = to_fun_hom (to_fun_ob G p''.1) (f'.2 ∘ f.2) ∘ natural_map (to_fun_hom G (f'.1 ∘ f.1)) p.2 : by esimp
      ... = (to_fun_hom (to_fun_ob G p''.1) f'.2 ∘ to_fun_hom (to_fun_ob G p''.1) f.2)
              ∘ natural_map (to_fun_hom G (f'.1 ∘ f.1)) p.2                   : by rewrite respect_comp
      ... = (to_fun_hom (to_fun_ob G p''.1) f'.2 ∘ to_fun_hom (to_fun_ob G p''.1) f.2)
              ∘ natural_map (to_fun_hom G f'.1 ∘ to_fun_hom G f.1) p.2        : by rewrite respect_comp
      ... = (to_fun_hom (to_fun_ob G p''.1) f'.2 ∘ to_fun_hom (to_fun_ob G p''.1) f.2)
              ∘ (natural_map (to_fun_hom G f'.1) p.2 ∘ natural_map (to_fun_hom G f.1) p.2) : by esimp
      ... = (to_fun_hom (to_fun_ob G p''.1) f'.2 ∘ to_fun_hom (to_fun_ob G p''.1) f.2)
              ∘ (natural_map (to_fun_hom G f'.1) p.2 ∘ natural_map (to_fun_hom G f.1) p.2) : by esimp
      ... = (to_fun_hom (to_fun_ob G p''.1) f'.2 ∘ natural_map (to_fun_hom G f'.1) p'.2)
              ∘ (to_fun_hom (to_fun_ob G p'.1) f.2 ∘ natural_map (to_fun_hom G f.1) p.2) :
                  square_prepostcompose (!naturality⁻¹ᵖ) _ _
      ... = Ghom G f' ∘ Ghom G f : by esimp

  definition functor_uncurry [reducible] : C ×c D ⇒ E :=
  functor.mk (functor_uncurry_ob G)
             (functor_uncurry_hom G)
             (functor_uncurry_id G)
             (functor_uncurry_comp G)

  theorem functor_uncurry_functor_curry : functor_uncurry (functor_curry F) = F :=
  functor_eq (λp, ap (to_fun_ob F) !prod.eta)
  begin
    intros [cd, cd', fg],
    cases cd with [c,d], cases cd' with [c',d'], cases fg with [f, g],
    apply concat, apply id_leftright,
    show (functor_uncurry (functor_curry F)) (f, g) = F (f,g),
      from calc
        (functor_uncurry (functor_curry F)) (f, g) = to_fun_hom F (id, g) ∘ to_fun_hom F (f, id) : by esimp
          ... = F (id ∘ f, g ∘ id) : respect_comp F (id,g) (f,id)
          ... = F (f, g ∘ id) : by rewrite id_left
          ... = F (f,g) : by rewrite id_right,
  end

  definition functor_curry_functor_uncurry_ob (c : C)
    : functor_curry (functor_uncurry G) c = G c :=
  begin
  fapply functor_eq,
   {intro d, apply idp},
   {intros [d, d', g],
     apply concat, apply id_leftright,
      show to_fun_hom (functor_curry (functor_uncurry G) c) g = to_fun_hom (G c) g,
      from calc
        to_fun_hom (functor_curry (functor_uncurry G) c) g
            = to_fun_hom (G c) g ∘ natural_map (to_fun_hom G (ID c)) d : by esimp
        ... = to_fun_hom (G c) g ∘ natural_map (ID (G c)) d : by rewrite respect_id
        ... = to_fun_hom (G c) g ∘ id : idp
        ... = to_fun_hom (G c) g : id_right}
  end

  theorem functor_curry_functor_uncurry : functor_curry (functor_uncurry G) = G :=
  begin
  fapply functor_eq, exact (functor_curry_functor_uncurry_ob G),
  intros [c, c', f],
  fapply nat_trans_eq_mk,
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

  definition prod_functor_equiv_functor_functor (C D E : Precategory)
    : (C ×c D ⇒ E) ≃ (C ⇒ E ^c D) :=
  equiv.MK functor_curry
           functor_uncurry
           functor_curry_functor_uncurry
           functor_uncurry_functor_curry


  definition functor_prod_flip (C D : Precategory) : C ×c D ⇒ D ×c C :=
  functor.mk (λp, (p.2, p.1))
             (λp p' h, (h.2, h.1))
             (λp, idp)
             (λp p' p'' h' h, idp)

  definition functor_prod_flip_functor_prod_flip (C D : Precategory)
    : functor_prod_flip D C ∘f (functor_prod_flip C D) = functor.id :=
  begin
  fapply functor_eq, {intro p, apply prod.eta},
  intros [p, p', h], cases p with [c, d], cases p' with [c', d'],
  apply id_leftright,
  end
end functor
open functor

namespace yoneda
  --should this be defined as "yoneda_embedding Cᵒᵖ"?
  definition contravariant_yoneda_embedding (C : Precategory) : Cᵒᵖ ⇒ set ^c C :=
  functor_curry !hom_functor

  definition yoneda_embedding (C : Precategory) : C ⇒ set ^c Cᵒᵖ :=
  functor_curry (!hom_functor ∘f !functor_prod_flip)

end yoneda
