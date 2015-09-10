/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

--note: modify definition in category.set
import .constructions.functor .constructions.hset .constructions.product .constructions.opposite
       .adjoint

open category eq category.ops functor prod.ops is_trunc iso

namespace yoneda
--  set_option class.conservative false

  definition representable_functor_assoc [C : Precategory] {a1 a2 a3 a4 a5 a6 : C}
    (f1 : hom a5 a6) (f2 : hom a4 a5) (f3 : hom a3 a4) (f4 : hom a2 a3) (f5 : hom a1 a2)
      : (f1 ∘ f2) ∘ f3 ∘ (f4 ∘ f5) = f1 ∘ (f2 ∘ f3 ∘ f4) ∘ f5 :=
  calc
        _ = f1 ∘ f2 ∘ f3 ∘ f4 ∘ f5     : by rewrite -assoc
      ... = f1 ∘ (f2 ∘ f3) ∘ f4 ∘ f5   : by rewrite -assoc
      ... = f1 ∘ ((f2 ∘ f3) ∘ f4) ∘ f5 : by rewrite -(assoc (f2 ∘ f3) _ _)
      ... = _                          : by rewrite (assoc f2 f3 f4)

  definition hom_functor.{u v} [constructor] (C : Precategory.{u v}) : Cᵒᵖ ×c C ⇒ set.{v} :=
  functor.mk
    (λ (x : Cᵒᵖ ×c C), @homset (Cᵒᵖ) C x.1 x.2)
    (λ (x y : Cᵒᵖ ×c C) (f : @category.precategory.hom (Cᵒᵖ ×c C) (Cᵒᵖ ×c C) x y) (h : @homset (Cᵒᵖ) C x.1 x.2),
       f.2 ∘[C] (h ∘[C] f.1))
    (λ x, @eq_of_homotopy _ _ _ (ID (@homset Cᵒᵖ C x.1 x.2)) (λ h, concat (by apply @id_left) (by apply @id_right)))
    (λ x y z g f,
       eq_of_homotopy (by intros; apply @representable_functor_assoc))
end yoneda

open is_equiv equiv

namespace functor
  open prod nat_trans
  variables {C D E : Precategory} (F : C ×c D ⇒ E) (G : C ⇒ E ^c D)
  definition functor_curry_ob [reducible] [constructor] (c : C) : E ^c D :=
  functor.mk (λd, F (c,d))
             (λd d' g, F (id, g))
             (λd, !respect_id)
             (λd₁ d₂ d₃ g' g, calc
               F (id, g' ∘ g) = F (id ∘ id, g' ∘ g) : by rewrite id_comp
                 ... = F ((id,g') ∘ (id, g))        : by esimp
                 ... = F (id,g') ∘ F (id, g)        : by rewrite respect_comp)

  local abbreviation Fob := @functor_curry_ob

  definition functor_curry_hom [constructor] ⦃c c' : C⦄ (f : c ⟶ c') : Fob F c ⟹ Fob F c' :=
  begin
    fapply @nat_trans.mk,
      {intro d, exact F (f, id)},
      {intro d d' g, calc
        F (id, g) ∘ F (f, id) = F (id ∘ f, g ∘ id) : respect_comp F
                   ... = F (f, g ∘ id)         : by rewrite id_left
                   ... = F (f, g)              : by rewrite id_right
                   ... = F (f ∘ id, g)         : by rewrite id_right
                   ... = F (f ∘ id, id ∘ g)    : by rewrite id_left
                   ... = F (f, id) ∘ F (id, g) : (respect_comp F (f, id) (id, g))⁻¹ᵖ
        }
  end
  local abbreviation Fhom := @functor_curry_hom

  theorem functor_curry_hom_def ⦃c c' : C⦄ (f : c ⟶ c') (d : D) :
    (Fhom F f) d = to_fun_hom F (f, id) := idp

  theorem functor_curry_id (c : C) : Fhom F (ID c) = nat_trans.id :=
  nat_trans_eq (λd, respect_id F _)

  theorem functor_curry_comp ⦃c c' c'' : C⦄ (f' : c' ⟶ c'') (f : c ⟶ c')
    : Fhom F (f' ∘ f) = Fhom F f' ∘n Fhom F f :=
  begin
    apply @nat_trans_eq,
    intro d, calc
    natural_map (Fhom F (f' ∘ f)) d = F (f' ∘ f, id) : by rewrite functor_curry_hom_def
      ... = F (f' ∘ f, id ∘ id)                      : by rewrite id_comp
      ... = F ((f',id) ∘ (f, id))                    : by esimp
      ... = F (f',id) ∘ F (f, id)                    : by rewrite [respect_comp F]
      ... = natural_map ((Fhom F f') ∘ (Fhom F f)) d : by esimp
  end

  definition functor_curry [reducible] [constructor] : C ⇒ E ^c D :=
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
   {intro d, reflexivity},
   {intro d d' g,
     apply concat, apply id_leftright,
      show to_fun_hom (functor_curry (functor_uncurry G) c) g = to_fun_hom (G c) g,
      from calc
        to_fun_hom (functor_curry (functor_uncurry G) c) g
            = to_fun_hom (G c) g ∘ natural_map (to_fun_hom G (ID c)) d : by esimp
        ... = to_fun_hom (G c) g ∘ natural_map (ID (G c)) d            : by rewrite respect_id
        ... = to_fun_hom (G c) g ∘ id                                  : by reflexivity
        ... = to_fun_hom (G c) g                                       : by rewrite id_right}
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

  definition prod_functor_equiv_functor_functor [constructor] (C D E : Precategory)
    : (C ×c D ⇒ E) ≃ (C ⇒ E ^c D) :=
  equiv.MK functor_curry
           functor_uncurry
           functor_curry_functor_uncurry
           functor_uncurry_functor_curry


  definition functor_prod_flip [constructor] (C D : Precategory) : C ×c D ⇒ D ×c C :=
  functor.mk (λp, (p.2, p.1))
             (λp p' h, (h.2, h.1))
             (λp, idp)
             (λp p' p'' h' h, idp)

  definition functor_prod_flip_functor_prod_flip (C D : Precategory)
    : functor_prod_flip D C ∘f (functor_prod_flip C D) = functor.id :=
  begin
  fapply functor_eq, {intro p, apply prod.eta},
  intro p p' h, cases p with c d, cases p' with c' d',
  apply id_leftright,
  end
end functor
open functor

namespace yoneda
  open category.set nat_trans lift

  /-
    These attributes make sure that the fields of the category "set" reduce to the right things
    However, we don't want to have them globally, because that will unfold the composition g ∘ f
    in a Category to category.category.comp g f
  -/
  local attribute Category.to.precategory category.to_precategory [constructor]

  -- should this be defined as "yoneda_embedding Cᵒᵖ"?
  definition contravariant_yoneda_embedding (C : Precategory) : Cᵒᵖ ⇒ set ^c C :=
  functor_curry !hom_functor

  definition yoneda_embedding (C : Precategory) : C ⇒ set ^c Cᵒᵖ :=
  functor_curry (!hom_functor ∘f !functor_prod_flip)

  notation `ɏ` := yoneda_embedding _

  definition yoneda_lemma_hom [constructor] {C : Precategory} (c : C) (F : Cᵒᵖ ⇒ set)
    (x : trunctype.carrier (F c)) : ɏ c ⟹ F :=
  begin
    fapply nat_trans.mk,
    { intro c', esimp [yoneda_embedding], intro f, exact F f x},
    { intro c' c'' f, esimp [yoneda_embedding], apply eq_of_homotopy, intro f',
      refine _ ⬝ ap (λy, to_fun_hom F y x) !(@id_left _ C)⁻¹,
      exact ap10 !(@respect_comp Cᵒᵖ set)⁻¹ x}
  end

  definition yoneda_lemma {C : Precategory} (c : C) (F : Cᵒᵖ ⇒ set) :
    homset (ɏ c) F ≅ lift_functor (F c) :=
  begin
    apply iso_of_equiv, esimp,
    fapply equiv.MK,
    { intro η, exact up (η c id)},
    { intro x, induction x with x, exact yoneda_lemma_hom c F x},
    { exact abstract begin intro x, induction x with x, esimp, apply ap up,
      exact ap10 !respect_id x end end},
    { exact abstract begin intro η, esimp, apply nat_trans_eq,
      intro c', esimp, apply eq_of_homotopy,
      intro f, esimp [yoneda_embedding] at f,
      transitivity (F f ∘ η c) id, reflexivity,
      rewrite naturality, esimp [yoneda_embedding], rewrite [id_left], apply ap _ !id_left end end},
  end

  theorem yoneda_lemma_natural_ob {C : Precategory} (F : Cᵒᵖ ⇒ set) {c c' : C} (f : c' ⟶ c)
    (η : ɏ c ⟹ F) :
     to_fun_hom (lift_functor ∘f F) f (to_hom (yoneda_lemma c F) η) =
     proof to_hom (yoneda_lemma c' F) (η ∘n to_fun_hom ɏ f) qed :=
  begin
    esimp [yoneda_lemma,yoneda_embedding], apply ap up,
    transitivity (F f ∘ η c) id, reflexivity,
    rewrite naturality,
    esimp [yoneda_embedding],
    apply ap (η c'),
    esimp [yoneda_embedding, Opposite],
    rewrite [+id_left,+id_right],
  end

  theorem yoneda_lemma_natural_functor.{u v} {C : Precategory.{u v}} (c : C) (F F' : Cᵒᵖ ⇒ set)
    (θ : F ⟹ F') (η : to_fun_ob ɏ c ⟹ F) :
     proof (lift_functor.{v u} ∘fn θ) c (to_hom (yoneda_lemma c F) η) qed =
     (to_hom (yoneda_lemma c F') proof (θ ∘n η : (to_fun_ob ɏ c : Cᵒᵖ ⇒ set) ⟹ F') qed) :=
  by reflexivity

  definition fully_faithful_yoneda_embedding [instance] (C : Precategory) :
    fully_faithful (ɏ : C ⇒ set ^c Cᵒᵖ) :=
  begin
    intro c c',
    fapply is_equiv_of_equiv_of_homotopy,
    { symmetry, transitivity _, apply @equiv_of_iso (homset _ _),
      rexact yoneda_lemma c (ɏ c'), esimp [yoneda_embedding], exact !equiv_lift⁻¹ᵉ},
    { intro f, apply nat_trans_eq, intro c, apply eq_of_homotopy, intro f',
      esimp [equiv.symm,equiv.trans],
      esimp [yoneda_lemma,yoneda_embedding,Opposite],
      rewrite [id_left,id_right]}
  end

  definition embedding_on_objects_yoneda_embedding (C : Category) :
    is_embedding (ɏ : C → Cᵒᵖ ⇒ set) :=
  begin
    intro c c', fapply is_equiv_of_equiv_of_homotopy,
    { exact !eq_equiv_iso ⬝e !iso_equiv_F_iso_F ⬝e !eq_equiv_iso⁻¹ᵉ},
    { intro p, induction p, esimp [equiv.trans, equiv.symm],
      esimp [to_fun_iso],
      rewrite -eq_of_iso_refl,
      apply ap eq_of_iso, apply iso_eq, esimp,
      apply nat_trans_eq, intro c',
      apply eq_of_homotopy, esimp [yoneda_embedding], intro f,
      rewrite [category.category.id_left], apply id_right}
  end

  definition is_representable {C : Precategory} (F : Cᵒᵖ ⇒ set) := Σ(c : C), ɏ c ≅ F

  definition is_hprop_representable {C : Category} (F : Cᵒᵖ ⇒ set)
    : is_hprop (is_representable F) :=
  begin
    fapply is_trunc_equiv_closed,
    { transitivity _, rotate 1,
      { apply sigma.sigma_equiv_sigma_id, intro c, exact !eq_equiv_iso},
      { apply fiber.sigma_char}},
    { apply function.is_hprop_fiber_of_is_embedding,
      apply embedding_on_objects_yoneda_embedding}
  end

end yoneda
