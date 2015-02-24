-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Floris van Doorn, Jakob von Raumer

import .basic

open eq precategory sigma sigma.ops equiv is_equiv function is_trunc

namespace morphism
  variables {ob : Type} [C : precategory ob] include C
  variables {a b c : ob} {g : b ⟶ c} {f : a ⟶ b} {h : b ⟶ a}
  inductive is_section    [class] (f : a ⟶ b) : Type
  := mk : ∀{g}, g ∘ f = id → is_section f
  inductive is_retraction [class] (f : a ⟶ b) : Type
  := mk : ∀{g}, f ∘ g = id → is_retraction f
  inductive is_iso        [class] (f : a ⟶ b) : Type
  := mk : ∀{g}, g ∘ f = id → f ∘ g = id → is_iso f

  attribute is_iso [multiple-instances]

  definition retraction_of (f : a ⟶ b) [H : is_section f] : hom b a :=
  is_section.rec (λg h, g) H
  definition section_of    (f : a ⟶ b) [H : is_retraction f] : hom b a :=
  is_retraction.rec (λg h, g) H
  definition inverse       (f : a ⟶ b) [H : is_iso f] : hom b a :=
  is_iso.rec (λg h1 h2, g) H

  postfix `⁻¹` := inverse

  theorem inverse_compose (f : a ⟶ b) [H : is_iso f] : f⁻¹ ∘ f = id :=
  is_iso.rec (λg h1 h2, h1) H

  theorem compose_inverse (f : a ⟶ b) [H : is_iso f] : f ∘ f⁻¹ = id :=
  is_iso.rec (λg h1 h2, h2) H

  theorem retraction_compose (f : a ⟶ b) [H : is_section f] : retraction_of f ∘ f = id :=
  is_section.rec (λg h, h) H

  theorem compose_section (f : a ⟶ b) [H : is_retraction f] : f ∘ section_of f = id :=
  is_retraction.rec (λg h, h) H

  theorem is_section_of_is_iso [instance] (f : a ⟶ b) [H : is_iso f] : is_section f :=
  is_section.mk !inverse_compose

  theorem is_retraction_of_is_iso [instance] (f : a ⟶ b) [H : is_iso f] : is_retraction f :=
  is_retraction.mk !compose_inverse

  theorem is_iso_id [instance] : is_iso (ID a) :=
  is_iso.mk !id_compose !id_compose

  theorem is_iso_inverse [instance] (f : a ⟶ b) [H : is_iso f] : is_iso (f⁻¹) :=
  is_iso.mk !compose_inverse !inverse_compose

  theorem left_inverse_eq_right_inverse {f : a ⟶ b} {g g' : hom b a}
      (Hl : g ∘ f = id) (Hr : f ∘ g' = id) : g = g' :=
  calc
    g = g ∘ id : !id_right
     ... = g ∘ f ∘ g' : Hr
     ... = (g ∘ f) ∘ g' : !assoc
     ... = id ∘ g' : Hl
     ... = g' : id_left

  theorem retraction_eq_intro [H : is_section f] (H2 : f ∘ h = id) : retraction_of f = h
  := left_inverse_eq_right_inverse !retraction_compose H2

  theorem section_eq_intro [H : is_retraction f] (H2 : h ∘ f = id) : section_of f = h
  := (left_inverse_eq_right_inverse H2 !compose_section)⁻¹

  theorem inverse_eq_intro_right [H : is_iso f] (H2 : f ∘ h = id) : f⁻¹ = h
  := left_inverse_eq_right_inverse !inverse_compose H2

  theorem inverse_eq_intro_left [H : is_iso f] (H2 : h ∘ f = id) : f⁻¹ = h
  := (left_inverse_eq_right_inverse H2 !compose_inverse)⁻¹

  theorem section_of_eq_retraction_of (f : a ⟶ b) [Hl : is_section f] [Hr : is_retraction f] :
      retraction_of f = section_of f :=
  retraction_eq_intro !compose_section

  theorem is_iso_of_is_retraction_of_is_section (f : a ⟶ b) [Hl : is_section f] [Hr : is_retraction f]
      : is_iso f :=
  is_iso.mk ((section_of_eq_retraction_of f) ▹ (retraction_compose f)) (compose_section f)

  theorem inverse_unique (H H' : is_iso f) : @inverse _ _ _ _ f H = @inverse _ _ _ _ f H' :=
  inverse_eq_intro_left !inverse_compose

  theorem inverse_involutive (f : a ⟶ b) [H : is_iso f] : (f⁻¹)⁻¹ = f :=
  inverse_eq_intro_right !inverse_compose

  theorem retraction_of_id : retraction_of (ID a) = id :=
  retraction_eq_intro !id_compose

  theorem section_of_id : section_of (ID a) = id :=
  section_eq_intro !id_compose

  theorem id_inverse [H : is_iso (ID a)] : (ID a)⁻¹ = id :=
  inverse_eq_intro_left !id_compose

  theorem is_section_comp [instance] [Hf : is_section f] [Hg : is_section g]
      : is_section (g ∘ f) :=
  have aux : retraction_of g ∘ g ∘ f = (retraction_of g ∘ g) ∘ f,
    from !assoc,
  is_section.mk
    (calc
      (retraction_of f ∘ retraction_of g) ∘ g ∘ f
            = retraction_of f ∘ retraction_of g ∘ g ∘ f : assoc
        ... = retraction_of f ∘ ((retraction_of g ∘ g) ∘ f) : aux
        ... = retraction_of f ∘ id ∘ f : {retraction_compose g}
        ... = retraction_of f ∘ f : {id_left f}
        ... = id : retraction_compose f)

  theorem is_retraction_comp [instance] [Hf : is_retraction f] [Hg : is_retraction g]
      : is_retraction (g ∘ f) :=
  have aux : f ∘ section_of f ∘ section_of g = (f ∘ section_of f) ∘ section_of g,
    from !assoc,
  is_retraction.mk
    (calc
      (g ∘ f) ∘ section_of f ∘ section_of g
            = g ∘ f ∘ section_of f ∘ section_of g : assoc
        ... = g ∘ (f ∘ section_of f) ∘ section_of g : aux
        ... = g ∘ id ∘ section_of g : compose_section f
        ... = g ∘ section_of g : {id_left (section_of g)}
        ... = id : compose_section)

  theorem is_inverse_comp [instance] [Hf : is_iso f] [Hg : is_iso g] : is_iso (g ∘ f) :=
  !is_iso_of_is_retraction_of_is_section

  structure isomorphic (a b : ob) :=
    (iso : hom a b)
    [is_iso : is_iso iso]

  infix `≅`:50 := morphism.isomorphic
  attribute isomorphic.is_iso [instance]

  namespace isomorphic

    definition refl (a : ob) : a ≅ a :=
    mk id

    definition symm ⦃a b : ob⦄ (H : a ≅ b) : b ≅ a :=
    mk (inverse (iso H))

    definition trans ⦃a b c : ob⦄ (H1 : a ≅ b) (H2 : b ≅ c) : a ≅ c :=
    mk (iso H2 ∘ iso H1)

  end isomorphic

  inductive is_mono [class] (f : a ⟶ b) : Type :=
  mk : (∀c (g h : hom c a), f ∘ g = f ∘ h → g = h) → is_mono f
  inductive is_epi  [class] (f : a ⟶ b) : Type :=
  mk : (∀c (g h : hom b c), g ∘ f = h ∘ f → g = h) → is_epi f

  theorem is_mono.elim [H : is_mono f] {g h : c ⟶ a} (H2 : f ∘ g = f ∘ h) : g = h
  := is_mono.rec (λH3, H3 c g h H2) H
  theorem is_epi.elim [H : is_epi f] {g h : b ⟶ c} (H2 : g ∘ f = h ∘ f) : g = h
  := is_epi.rec  (λH3, H3 c g h H2) H

  theorem is_mono_of_is_section [instance] (f : a ⟶ b) [H : is_section f] : is_mono f :=
  is_mono.mk
    (λ c g h H,
      calc
        g = id ∘ g : id_left
      ... = (retraction_of f ∘ f) ∘ g : retraction_compose f
      ... = retraction_of f ∘ f ∘ g : assoc
      ... = retraction_of f ∘ f ∘ h : H
      ... = (retraction_of f ∘ f) ∘ h : assoc
      ... = id ∘ h : retraction_compose f
      ... = h : id_left)

  theorem is_epi_of_is_retraction [instance] (f : a ⟶ b) [H : is_retraction f] : is_epi f :=
  is_epi.mk
    (λ c g h H,
      calc
        g = g ∘ id : id_right
      ... = g ∘ f ∘ section_of f : compose_section f
      ... = (g ∘ f) ∘ section_of f : assoc
      ... = (h ∘ f) ∘ section_of f : H
      ... = h ∘ f ∘ section_of f : assoc
      ... = h ∘ id : compose_section f
      ... = h : id_right)

  theorem is_mono_comp [instance] [Hf : is_mono f] [Hg : is_mono g] : is_mono (g ∘ f) :=
  is_mono.mk
    (λ d h₁ h₂ H,
      have H2 : g ∘ (f ∘ h₁) = g ∘ (f ∘ h₂),
        from calc g ∘ (f ∘ h₁) = (g ∘ f) ∘ h₁ : !assoc
                          ... = (g ∘ f) ∘ h₂ : H
                          ... = g ∘ (f ∘ h₂) : !assoc, is_mono.elim (is_mono.elim H2))

  theorem is_epi_comp  [instance] [Hf : is_epi f] [Hg : is_epi g] : is_epi  (g ∘ f) :=
  is_epi.mk
    (λ d h₁ h₂ H,
      have H2 : (h₁ ∘ g) ∘ f = (h₂ ∘ g) ∘ f,
        from calc (h₁ ∘ g) ∘ f = h₁ ∘ g ∘ f : !assoc
                          ... = h₂ ∘ g ∘ f : H
                          ... = (h₂ ∘ g) ∘ f: !assoc, is_epi.elim (is_epi.elim H2))

end morphism

namespace morphism
--rewrite lemmas for inverses, modified from
--https://github.com/JasonGross/HoTT-categories/blob/master/theories/Categories/Category/Morphisms.v
  namespace iso
  section
  variables {ob : Type} [C : precategory ob] include C
  variables {a b c d : ob}                                         (f : b ⟶ a)
                           (r : c ⟶ d) (q : b ⟶ c) (p : a ⟶ b)
                           (g : d ⟶ c)
  variable [Hq : is_iso q] include Hq
  theorem compose_pV : q ∘ q⁻¹ = id := !compose_inverse
  theorem compose_Vp : q⁻¹ ∘ q = id := !inverse_compose
  theorem compose_V_pp : q⁻¹ ∘ (q ∘ p) = p :=
  calc
    q⁻¹ ∘ (q ∘ p) = (q⁻¹ ∘ q) ∘ p : assoc (q⁻¹) q p
      ... = id ∘ p : inverse_compose q
      ... = p : id_left p
  theorem compose_p_Vp : q ∘ (q⁻¹ ∘ g) = g :=
  calc
     q ∘ (q⁻¹ ∘ g)  = (q ∘ q⁻¹) ∘ g : assoc q (q⁻¹) g
      ... = id ∘ g : compose_inverse q
      ... = g : id_left g
  theorem compose_pp_V : (r ∘ q) ∘ q⁻¹ = r :=
  calc
    (r ∘ q) ∘ q⁻¹ = r ∘ q ∘ q⁻¹ : assoc r q (q⁻¹)⁻¹
      ... = r ∘ id : compose_inverse q
      ... = r : id_right r
  theorem compose_pV_p : (f ∘ q⁻¹) ∘ q = f :=
  calc
    (f ∘ q⁻¹) ∘ q = f ∘ q⁻¹ ∘ q : assoc f (q⁻¹) q⁻¹
      ... = f ∘ id : inverse_compose q
      ... = f : id_right f

  theorem con_inv [H' : is_iso p] [Hpq : is_iso (q ∘ p)] : (q ∘ p)⁻¹ = p⁻¹ ∘ q⁻¹ :=
  have H1 : (p⁻¹ ∘ q⁻¹) ∘ q ∘ p = p⁻¹ ∘ (q⁻¹ ∘ (q ∘ p)), from assoc (p⁻¹) (q⁻¹) (q ∘ p)⁻¹,
  have H2 : (p⁻¹) ∘ (q⁻¹ ∘ (q ∘ p)) = p⁻¹ ∘ p, from ap _ (compose_V_pp q p),
  have H3 : p⁻¹ ∘ p = id, from inverse_compose p,
  inverse_eq_intro_left (H1 ⬝ H2 ⬝ H3)

  --the proof using calc is hard for the unifier (needs ~90k steps)
  -- inverse_eq_intro_left
  --   (calc
  --     (p⁻¹ ∘ (q⁻¹)) ∘ q ∘ p = p⁻¹ ∘ (q⁻¹ ∘ (q ∘ p)) : assoc (p⁻¹) (q⁻¹) (q ∘ p)⁻¹
  --     ... = (p⁻¹) ∘ p : congr_arg (λx, p⁻¹ ∘ x) (compose_V_pp q p)
  --     ... = id : inverse_compose p)
  theorem inv_con_inv_left [H' : is_iso g] : (q⁻¹ ∘ g)⁻¹ = g⁻¹ ∘ q :=
  inverse_involutive q ▹ con_inv (q⁻¹) g

  theorem inv_con_inv_right [H' : is_iso f] : (q ∘ f⁻¹)⁻¹ = f ∘ q⁻¹ :=
  inverse_involutive f ▹ con_inv q (f⁻¹)

  theorem inv_con_inv_inv [H' : is_iso r] : (q⁻¹ ∘ r⁻¹)⁻¹ = r ∘ q :=
  inverse_involutive r ▹ inv_con_inv_left q (r⁻¹)

  end
  section
  variables {ob : Type} {C : precategory ob} include C
  variables {d           c           b           a : ob}
                          {i : b ⟶ c} {f : b ⟶ a}
              {r : c ⟶ d} {q : b ⟶ c} {p : a ⟶ b}
              {g : d ⟶ c} {h : c ⟶ b}
                   {x : b ⟶ d} {z : a ⟶ c}
                   {y : d ⟶ b} {w : c ⟶ a}
  variable [Hq : is_iso q] include Hq

  theorem con_eq_of_eq_inv_con (H : y = q⁻¹ ∘ g) : q ∘ y = g := H⁻¹ ▹ compose_p_Vp q g
  theorem con_eq_of_eq_con_inv (H : w = f ∘ q⁻¹) : w ∘ q = f := H⁻¹ ▹ compose_pV_p f q
  theorem inv_con_eq_of_eq_con (H : z = q ∘ p) : q⁻¹ ∘ z = p := H⁻¹ ▹ compose_V_pp q p
  theorem con_inv_eq_of_eq_con (H : x = r ∘ q) : x ∘ q⁻¹ = r := H⁻¹ ▹ compose_pp_V r q
  theorem eq_con_of_inv_con_eq (H : q⁻¹ ∘ g = y) : g = q ∘ y := con_eq_of_eq_inv_con (H⁻¹)⁻¹
  theorem eq_con_of_con_inv_eq (H : f ∘ q⁻¹ = w) : f = w ∘ q := con_eq_of_eq_con_inv (H⁻¹)⁻¹
  theorem eq_inv_con_of_con_eq (H : q ∘ p = z) : p = q⁻¹ ∘ z := inv_con_eq_of_eq_con (H⁻¹)⁻¹
  theorem eq_con_inv_of_con_eq (H : r ∘ q = x) : r = x ∘ q⁻¹ := con_inv_eq_of_eq_con (H⁻¹)⁻¹
  theorem eq_inv_of_con_eq_idp' (H : h ∘ q = id) : h = q⁻¹ := inverse_eq_intro_left H⁻¹
  theorem eq_inv_of_con_eq_idp (H : q ∘ h = id) : h = q⁻¹ := inverse_eq_intro_right H⁻¹
  theorem eq_of_con_inv_eq_idp (H : i ∘ q⁻¹ = id) : i = q := eq_inv_of_con_eq_idp' H ⬝ inverse_involutive q
  theorem eq_of_inv_con_eq_idp (H : q⁻¹ ∘ i = id) : i = q := eq_inv_of_con_eq_idp H ⬝ inverse_involutive q
  theorem eq_of_idp_eq_con_inv (H : id = i ∘ q⁻¹) : q = i := eq_of_con_inv_eq_idp (H⁻¹)⁻¹
  theorem eq_of_idp_eq_inv_con (H : id = q⁻¹ ∘ i) : q = i := eq_of_inv_con_eq_idp (H⁻¹)⁻¹
  theorem inv_eq_of_idp_eq_con (H : id = h ∘ q) : q⁻¹ = h := eq_inv_of_con_eq_idp' (H⁻¹)⁻¹
  theorem inv_eq_of_idp_eq_con' (H : id = q ∘ h) : q⁻¹ = h := eq_inv_of_con_eq_idp (H⁻¹)⁻¹
  end
  end iso

end morphism
