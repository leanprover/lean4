/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.precategory.yoneda
Authors: Floris van Doorn
-/

--note: modify definition in category.set
import algebra.category.constructions .iso

open category eq category.ops functor prod.ops is_trunc

set_option pp.beta true
namespace yoneda
  set_option class.conservative false

  --TODO: why does this take so much steps? (giving more information than "assoc" hardly helps)
  definition representable_functor_assoc [C : Precategory] {a1 a2 a3 a4 a5 a6 : C}
    (f1 : hom a5 a6) (f2 : hom a4 a5) (f3 : hom a3 a4) (f4 : hom a2 a3) (f5 : hom a1 a2)
      : (f1 ∘ f2) ∘ f3 ∘ (f4 ∘ f5) = f1 ∘ (f2 ∘ f3 ∘ f4) ∘ f5 :=
  calc
        _ = f1 ∘ f2 ∘ f3 ∘ f4 ∘ f5     : by rewrite -assoc
      ... = f1 ∘ (f2 ∘ f3) ∘ f4 ∘ f5   : by rewrite -assoc
      ... = f1 ∘ ((f2 ∘ f3) ∘ f4) ∘ f5 : by rewrite -(assoc (f2 ∘ f3) _ _)
      ... = _                          : by rewrite (assoc f2 f3 f4)

  --disturbing behaviour: giving the type of f "(x ⟶ y)" explicitly makes the unifier loop
  definition hom_functor (C : Precategory) : Cᵒᵖ ×c C ⇒ set :=
  functor.mk (λ(x : Cᵒᵖ ×c C), homset x.1 x.2)
             (λ(x y : Cᵒᵖ ×c C) (f : _) (h : homset x.1 x.2), f.2 ∘⁅ C ⁆ (h ∘⁅ C ⁆ f.1))
             begin
               intro x, apply eq_of_homotopy, intro h, exact (!id_left ⬝ !id_right)
             end
             begin
               intros (x, y, z, g, f), apply eq_of_homotopy, intro h,
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
               F (id, g' ∘ g) = F (id ∘ id, g' ∘ g) : {(id_comp c)⁻¹}
                 ... = F ((id,g') ∘ (id, g)) : idp
                 ... = F (id,g') ∘ F (id, g) : by rewrite (respect_comp F))

  local abbreviation Fob := @functor_curry_ob

  definition functor_curry_hom ⦃c c' : C⦄ (f : c ⟶ c') : Fob F c ⟹ Fob F c' :=
  nat_trans.mk (λd, F (f, id))
               (λd d' g, calc
                 F (id, g) ∘ F (f, id) = F (id ∘ f, g ∘ id) : respect_comp F
                   ... = F (f, g ∘ id)      : by rewrite id_left
                   ... = F (f, g)           : by rewrite id_right
                   ... = F (f ∘ id, g)      : by rewrite id_right
                   ... = F (f ∘ id, id ∘ g) : by rewrite id_left
                   ... = F (f, id) ∘ F (id, g) :  (respect_comp F (f, id) (id, g))⁻¹ᵖ)

  local abbreviation Fhom := @functor_curry_hom

  definition functor_curry_hom_def ⦃c c' : C⦄ (f : c ⟶ c') (d : D) :
    (Fhom F f) d = to_fun_hom F (f, id) := idp

  theorem functor_curry_id (c : C) : Fhom F (ID c) = nat_trans.id :=
  nat_trans_eq_mk (λd, respect_id F _)

  theorem functor_curry_comp ⦃c c' c'' : C⦄ (f' : c' ⟶ c'') (f : c ⟶ c')
    : Fhom F (f' ∘ f) = Fhom F f' ∘n Fhom F f :=
  nat_trans_eq_mk (λd, calc
    natural_map (Fhom F (f' ∘ f)) d = F (f' ∘ f, id) : functor_curry_hom_def
      ... = F (f' ∘ f, id ∘ id) : {(id_comp d)⁻¹}
      ... = F ((f',id) ∘ (f, id)) : idp
      ... = F (f',id) ∘ F (f, id) : respect_comp F
      ... = natural_map ((Fhom F f') ∘ (Fhom F f)) d : idp)

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
    Ghom G (ID p) = to_fun_hom (to_fun_ob G p.1) id ∘ natural_map (to_fun_hom G id) p.2 : idp
      ... = id ∘ natural_map (to_fun_hom G id) p.2 : ap (λx, x ∘ _) (respect_id (to_fun_ob G p.1) p.2)
      ... = id ∘ natural_map nat_trans.id p.2 : {respect_id G p.1}
      ... = id : id_comp

  theorem functor_uncurry_comp ⦃p p' p'' : C ×c D⦄ (f' : p' ⟶ p'') (f : p ⟶ p')
    : Ghom G (f' ∘ f) = Ghom G f' ∘ Ghom G f :=
  calc
    Ghom G (f' ∘ f)
          = to_fun_hom (to_fun_ob G p''.1) (f'.2 ∘ f.2) ∘ natural_map (to_fun_hom G (f'.1 ∘ f.1)) p.2 : idp
      ... = (to_fun_hom (to_fun_ob G p''.1) f'.2 ∘ to_fun_hom (to_fun_ob G p''.1) f.2)
              ∘ natural_map (to_fun_hom G (f'.1 ∘ f.1)) p.2 : {respect_comp (to_fun_ob G p''.1) f'.2 f.2}
      ... = (to_fun_hom (to_fun_ob G p''.1) f'.2 ∘ to_fun_hom (to_fun_ob G p''.1) f.2)
              ∘ natural_map (to_fun_hom G f'.1 ∘ to_fun_hom G f.1) p.2 : {respect_comp G f'.1 f.1}
      ... = (to_fun_hom (to_fun_ob G p''.1) f'.2 ∘ to_fun_hom (to_fun_ob G p''.1) f.2)
              ∘ (natural_map (to_fun_hom G f'.1) p.2 ∘ natural_map (to_fun_hom G f.1) p.2) : idp
      ... = (to_fun_hom (to_fun_ob G p''.1) f'.2 ∘ to_fun_hom (to_fun_ob G p''.1) f.2)
              ∘ (natural_map (to_fun_hom G f'.1) p.2 ∘ natural_map (to_fun_hom G f.1) p.2) : idp
      ... = (to_fun_hom (to_fun_ob G p''.1) f'.2 ∘ natural_map (to_fun_hom G f'.1) p'.2)
              ∘ (to_fun_hom (to_fun_ob G p'.1) f.2 ∘ natural_map (to_fun_hom G f.1) p.2) :
                  square_prepostcompose (!naturality⁻¹ᵖ) _ _
      ... = Ghom G f' ∘ Ghom G f : idp

  definition functor_uncurry [reducible] : C ×c D ⇒ E :=
  functor.mk (functor_uncurry_ob G)
             (functor_uncurry_hom G)
             (functor_uncurry_id G)
             (functor_uncurry_comp G)
  -- open pi
  -- definition functor_eq_mk'1 {F₁ F₂ : C → D} {H₁ : Π(a b : C), hom a b → hom (F₁ a) (F₁ b)}
  --   {H₂ : Π(a b : C), hom a b → hom (F₂ a) (F₂ b)} (id₁ id₂ comp₁ comp₂)
  --   (pF : F₁ = F₂) (pH : Π(a b : C) (f : hom a b), pF ▹ (H₁ a b f) = H₂ a b f)
  --     : functor.mk F₁ H₁ id₁ comp₁ = functor.mk F₂ H₂ id₂ comp₂ :=
  -- functor_eq_mk'' id₁ id₂ comp₁ comp₂ pF
  --   (eq_of_homotopy (λc, eq_of_homotopy (λc', eq_of_homotopy (λf,
  --     begin
  --      apply concat, rotate_left 1, exact (pH c c' f),
  --      apply concat, rotate_left 1,
  --      exact (pi_transport_constant pF (H₁ c c') f),
  --      apply (apD10' f),
  --      apply concat, rotate_left 1,
  --      exact (pi_transport_constant pF (H₁ c) c'),
  --      apply (apD10' c'),
  --      apply concat, rotate_left 1,
  --      exact (pi_transport_constant pF H₁ c),
  --      apply idp
  --     end))))

  -- definition functor_eq_mk1 {F₁ F₂ : C ⇒ D} : Π(p : to_fun_ob F₁ = to_fun_ob F₂),
  --   (Π(a b : C) (f : hom a b), transport (λF, hom (F a) (F b)) p (F₁ f) = F₂ f)
  --     → F₁ = F₂ :=
  -- functor.rec_on F₁ (λO₁ H₁ id₁ comp₁, functor.rec_on F₂ (λO₂ H₂ id₂ comp₂ p, !functor_eq_mk'1))


  set_option pp.full_names true
  open tactic
  print raw id
  --set_option pp.notation false
  definition functor_uncurry_functor_curry : functor_uncurry (functor_curry F) = F :=
  functor_eq_mk (λp, ap (to_fun_ob F) !prod.eta)
  begin
    intros (cd, cd', fg),
    cases cd with (c,d), cases cd' with (c',d'), cases fg with (f,g),
    have H : (functor_uncurry (functor_curry F)) (f, g) = F (f,g),
      from calc
        (functor_uncurry (functor_curry F)) (f, g) = to_fun_hom F (id, g) ∘ to_fun_hom F (f, id) : idp
          ... = F (id ∘ f, g ∘ id) : respect_comp F (id,g) (f,id)
          ... = F (f, g ∘ id) : {id_left f}
          ... = F (f,g) : {id_right g},
    rewrite H,
    apply sorry
  end
  --set_option pp.implicit true
  definition functor_curry_functor_uncurry : functor_curry (functor_uncurry G) = G :=
  begin
    fapply functor_eq_mk,
     {intro c,
      fapply functor_eq_mk,
       {intro d, apply idp},
       {intros (d, d', g),
        have H : to_fun_hom (functor_curry (functor_uncurry G) c) g = to_fun_hom (G c) g,
        from calc
          to_fun_hom (functor_curry (functor_uncurry G) c) g
                = to_fun_hom (G c) g ∘ natural_map (to_fun_hom G (ID c)) d : idp
            ... = to_fun_hom (G c) g ∘ natural_map (ID (G c)) d
                   : ap (λx, to_fun_hom (G c) g ∘ natural_map x d) (respect_id G c)
            ... = to_fun_hom (G c) g : id_right,
        rewrite H,
--        esimp {idp},
        apply sorry
       }
     },
    apply sorry
  end

  definition equiv_functor_curry : (C ×c D ⇒ E) ≃ (C ⇒ E ^c D) :=
  equiv.MK functor_curry
           functor_uncurry
           functor_curry_functor_uncurry
           functor_uncurry_functor_curry


  definition functor_prod_flip_ob : C ×c D ⇒ D ×c C :=
  functor.mk sorry sorry sorry sorry


  definition contravariant_yoneda_embedding : Cᵒᵖ ⇒ set ^c C :=
  functor_curry !yoneda.hom_functor

end functor

-- Coq uses unit/counit definitions as basic

-- open yoneda precategory.product precategory.opposite functor morphism
--   --universe levels are given explicitly because Lean uses 6 variables otherwise

--   structure adjoint.{u v} [C D : Precategory.{u v}] (F : C ⇒ D) (G : D ⇒ C) : Type.{max u v} :=
--   (nat_iso : (hom_functor D) ∘f (prod_functor (opposite_functor F) (functor.ID D)) ⟹
--              (hom_functor C) ∘f (prod_functor (functor.ID (Cᵒᵖ)) G))
--   (is_iso_nat_iso : is_iso nat_iso)

--   infix `⊣`:55 := adjoint

-- namespace adjoint
--   universe variables l1 l2
--   variables [C D : Precategory.{l1 l2}] (F : C ⇒ D) (G : D ⇒ C)



-- end adjoint
