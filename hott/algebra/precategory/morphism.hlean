/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.category.morphism
Author: Floris van Doorn, Jakob von Raumer
-/

import algebra.precategory.basic

open eq category sigma sigma.ops equiv is_equiv is_trunc

namespace morphism
  structure is_section [class] {ob : Type} [C : precategory ob] {a b : ob} (f : a ⟶ b) :=
    {retraction_of : b ⟶ a}
    (retraction_compose : retraction_of ∘ f = id)
  structure is_retraction [class] {ob : Type} [C : precategory ob] {a b : ob} (f : a ⟶ b) :=
    {section_of : b ⟶ a}
    (compose_section : f ∘ section_of = id)
  structure is_iso [class] {ob : Type} [C : precategory ob] {a b : ob} (f : a ⟶ b) :=
    {inverse : b ⟶ a}
    (inverse_compose : inverse ∘ f = id)
    (compose_inverse : f ∘ inverse = id)

  attribute is_iso [multiple-instances]
  open is_section is_retraction is_iso
  definition retraction_of [reducible] := @is_section.retraction_of
  definition retraction_compose [reducible] := @is_section.retraction_compose
  definition section_of [reducible] := @is_retraction.section_of
  definition compose_section [reducible] := @is_retraction.compose_section
  definition inverse [reducible] := @is_iso.inverse
  definition inverse_compose [reducible] := @is_iso.inverse_compose
  definition compose_inverse [reducible] := @is_iso.compose_inverse
  postfix `⁻¹` := inverse
  --a second notation for the inverse, which is not overloaded
  postfix [parsing-only] `⁻¹ʰ`:std.prec.max_plus := inverse

  variables {ob : Type} [C : precategory ob]
  variables {a b c : ob} {g : b ⟶ c} {f : a ⟶ b} {h : b ⟶ a}
  include C

  definition iso_imp_retraction [instance] [priority 300] [reducible]
    (f : a ⟶ b) [H : is_iso f] : is_section f :=
  is_section.mk !inverse_compose

  definition iso_imp_section [instance] [priority 300] [reducible]
    (f : a ⟶ b) [H : is_iso f] : is_retraction f :=
  is_retraction.mk !compose_inverse

  definition is_iso_id [instance] [priority 500] (a : ob) : is_iso (ID a) :=
  is_iso.mk !id_compose !id_compose

  definition is_iso_inverse [instance] [priority 200] (f : a ⟶ b) [H : is_iso f] : is_iso f⁻¹ :=
  is_iso.mk !compose_inverse !inverse_compose

  definition left_inverse_eq_right_inverse {f : a ⟶ b} {g g' : hom b a}
      (Hl : g ∘ f = id) (Hr : f ∘ g' = id) : g = g' :=
  by rewrite [-(id_right g), -Hr, assoc, Hl, id_left]

  definition retraction_eq_intro [H : is_section f] (H2 : f ∘ h = id) : retraction_of f = h :=
  left_inverse_eq_right_inverse !retraction_compose H2

  definition section_eq_intro [H : is_retraction f] (H2 : h ∘ f = id) : section_of f = h :=
  (left_inverse_eq_right_inverse H2 !compose_section)⁻¹

  definition inverse_eq_intro_right [H : is_iso f] (H2 : f ∘ h = id) : f⁻¹ = h :=
  left_inverse_eq_right_inverse !inverse_compose H2

  definition inverse_eq_intro_left [H : is_iso f] (H2 : h ∘ f = id) : f⁻¹ = h :=
  (left_inverse_eq_right_inverse H2 !compose_inverse)⁻¹

  definition section_eq_retraction (f : a ⟶ b) [Hl : is_section f] [Hr : is_retraction f] :
      retraction_of f = section_of f :=
  retraction_eq_intro !compose_section

  definition section_retraction_imp_iso (f : a ⟶ b) [Hl : is_section f] [Hr : is_retraction f]
    : is_iso f :=
  is_iso.mk ((section_eq_retraction f) ▹ (retraction_compose f)) (compose_section f)

  definition inverse_unique (H H' : is_iso f) : @inverse _ _ _ _ f H = @inverse _ _ _ _ f H' :=
  inverse_eq_intro_left !inverse_compose

  definition inverse_involutive (f : a ⟶ b) [H : is_iso f] : (f⁻¹)⁻¹ = f :=
  inverse_eq_intro_right !inverse_compose

  definition retraction_of_id (a : ob) : retraction_of (ID a) = id :=
  retraction_eq_intro !id_compose

  definition section_of_id (a : ob) : section_of (ID a) = id :=
  section_eq_intro !id_compose

  definition iso_of_id (a : ob) [H : is_iso (ID a)] : (ID a)⁻¹ = id :=
  inverse_eq_intro_left !id_compose

  definition composition_is_section [instance] [priority 150] (g : b ⟶ c) (f : a ⟶ b)
    [Hf : is_section f] [Hg : is_section g] : is_section (g ∘ f) :=
  is_section.mk
    (show (retraction_of f ∘ retraction_of g) ∘ g ∘ f = id,
     by rewrite [-assoc, assoc _ g f, retraction_compose, id_left, retraction_compose])

  definition composition_is_retraction [instance] [priority 150] (g : b ⟶ c) (f : a ⟶ b)
    [Hf : is_retraction f] [Hg : is_retraction g] : is_retraction (g ∘ f) :=
  is_retraction.mk
    (show (g ∘ f) ∘ section_of f ∘ section_of g = id,
     by rewrite [-assoc, {f ∘ _}assoc, compose_section, id_left, compose_section])

  definition composition_is_inverse [instance] [priority 150] (g : b ⟶ c) (f : a ⟶ b)
    [Hf : is_iso f] [Hg : is_iso g] : is_iso (g ∘ f) :=
  !section_retraction_imp_iso

  structure isomorphic (a b : ob) :=
    (iso : hom a b)
    [struct : is_iso iso]

  infix `≅`:50 := morphism.isomorphic
  attribute isomorphic.struct [instance] [priority 400]

  namespace isomorphic
    attribute to_fun [coercion]

    protected definition refl (a : ob) : a ≅ a :=
    mk (ID a)

    protected definition symm ⦃a b : ob⦄ (H : a ≅ b) : b ≅ a :=
    mk (iso H)⁻¹

    protected definition trans ⦃a b c : ob⦄ (H1 : a ≅ b) (H2 : b ≅ c) : a ≅ c :=
    mk (iso H2 ∘ iso H1)

  end isomorphic

  structure is_mono [class] (f : a ⟶ b) :=
    (elim : ∀c (g h : hom c a), f ∘ g = f ∘ h → g = h)
  structure is_epi  [class] (f : a ⟶ b) :=
    (elim : ∀c (g h : hom b c), g ∘ f = h ∘ f → g = h)

  definition is_mono_of_is_section [instance] (f : a ⟶ b) [H : is_section f] : is_mono f :=
  is_mono.mk
    (λ c g h H,
      calc
        g = id ∘ g                    : by rewrite id_left
      ... = (retraction_of f ∘ f) ∘ g : by rewrite -retraction_compose
      ... = (retraction_of f ∘ f) ∘ h : by rewrite [-assoc, H, -assoc]
      ... = id ∘ h                    : by rewrite retraction_compose
      ... = h                         : by rewrite id_left)

  definition is_epi_of_is_retraction [instance] (f : a ⟶ b) [H : is_retraction f] : is_epi f :=
  is_epi.mk
    (λ c g h H,
      calc
        g = g ∘ id                 : by rewrite id_right
      ... = g ∘ f ∘ section_of f   : by rewrite -compose_section
      ... = h ∘ f ∘ section_of f   : by rewrite [assoc, H, -assoc]
      ... = h ∘ id                 : by rewrite compose_section
      ... = h                      : by rewrite id_right)

  definition is_mono_comp [instance] (g : b ⟶ c) (f : a ⟶ b) [Hf : is_mono f] [Hg : is_mono g]
    : is_mono (g ∘ f) :=
  is_mono.mk
    (λ d h₁ h₂ H,
    have H2 : g ∘ (f ∘ h₁) = g ∘ (f ∘ h₂),
    begin
      rewrite *assoc, exact H
    end,
    !is_mono.elim (!is_mono.elim H2))

  definition is_epi_comp  [instance] (g : b ⟶ c) (f : a ⟶ b) [Hf : is_epi f] [Hg : is_epi g]
    : is_epi  (g ∘ f) :=
  is_epi.mk
    (λ d h₁ h₂ H,
    have H2 : (h₁ ∘ g) ∘ f = (h₂ ∘ g) ∘ f,
    begin
      rewrite -*assoc, exact H
    end,
    !is_epi.elim (!is_epi.elim H2))

end morphism

namespace morphism
  /-
  rewrite lemmas for inverses, modified from
  https://github.com/JasonGross/HoTT-categories/blob/master/theories/Categories/Category/Morphisms.v
  -/
  namespace iso
  section
  variables {ob : Type} [C : precategory ob] include C
  variables {a b c d : ob}                         (f : b ⟶ a)
                           (r : c ⟶ d) (q : b ⟶ c) (p : a ⟶ b)
                           (g : d ⟶ c)
  variable [Hq : is_iso q] include Hq
  definition compose_pV : q ∘ q⁻¹ = id := !compose_inverse
  definition compose_Vp : q⁻¹ ∘ q = id := !inverse_compose
  definition compose_V_pp : q⁻¹ ∘ (q ∘ p) = p :=
   by rewrite [assoc, inverse_compose, id_left]
  definition compose_p_Vp : q ∘ (q⁻¹ ∘ g) = g :=
   by rewrite [assoc, compose_inverse, id_left]
  definition compose_pp_V : (r ∘ q) ∘ q⁻¹ = r :=
  by rewrite [-assoc, compose_inverse, id_right]
  definition compose_pV_p : (f ∘ q⁻¹) ∘ q = f :=
  by rewrite [-assoc, inverse_compose, id_right]

  definition con_inv [Hp : is_iso p] [Hpq : is_iso (q ∘ p)] : (q ∘ p)⁻¹ʰ = p⁻¹ʰ ∘ q⁻¹ʰ :=
  inverse_eq_intro_left
    (show (p⁻¹ʰ ∘ q⁻¹ʰ) ∘ q ∘ p = id, from
     by rewrite [-assoc, compose_V_pp, inverse_compose])

  definition inv_con_inv_left [H' : is_iso g] : (q⁻¹ ∘ g)⁻¹ = g⁻¹ ∘ q :=
  inverse_involutive q ▹ con_inv q⁻¹ g

  definition inv_con_inv_right [H' : is_iso f] : (q ∘ f⁻¹)⁻¹ = f ∘ q⁻¹ :=
  inverse_involutive f ▹ con_inv q f⁻¹

  definition inv_con_inv_inv [H' : is_iso r] : (q⁻¹ ∘ r⁻¹)⁻¹ = r ∘ q :=
  inverse_involutive r ▹ inv_con_inv_left q r⁻¹
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

  definition con_eq_of_eq_inv_con (H : y = q⁻¹ ∘ g) : q ∘ y = g := H⁻¹ ▹ compose_p_Vp q g
  definition con_eq_of_eq_con_inv (H : w = f ∘ q⁻¹) : w ∘ q = f := H⁻¹ ▹ compose_pV_p f q
  definition inv_con_eq_of_eq_con (H : z = q ∘ p) : q⁻¹ ∘ z = p := H⁻¹ ▹ compose_V_pp q p
  definition con_inv_eq_of_eq_con (H : x = r ∘ q) : x ∘ q⁻¹ = r := H⁻¹ ▹ compose_pp_V r q
  definition eq_con_of_inv_con_eq (H : q⁻¹ ∘ g = y) : g = q ∘ y := (con_eq_of_eq_inv_con H⁻¹)⁻¹
  definition eq_con_of_con_inv_eq (H : f ∘ q⁻¹ = w) : f = w ∘ q := (con_eq_of_eq_con_inv H⁻¹)⁻¹
  definition eq_inv_con_of_con_eq (H : q ∘ p = z) : p = q⁻¹ ∘ z := (inv_con_eq_of_eq_con H⁻¹)⁻¹
  definition eq_con_inv_of_con_eq (H : r ∘ q = x) : r = x ∘ q⁻¹ := (con_inv_eq_of_eq_con H⁻¹)⁻¹
  definition eq_inv_of_con_eq_idp' (H : h ∘ q = id) : h = q⁻¹ := (inverse_eq_intro_left H)⁻¹
  definition eq_inv_of_con_eq_idp (H : q ∘ h = id) : h = q⁻¹ := (inverse_eq_intro_right H)⁻¹
  definition eq_of_con_inv_eq_idp (H : i ∘ q⁻¹ = id) : i = q :=
  eq_inv_of_con_eq_idp' H ⬝ inverse_involutive q
  definition eq_of_inv_con_eq_idp (H : q⁻¹ ∘ i = id) : i = q :=
  eq_inv_of_con_eq_idp H ⬝ inverse_involutive q
  definition eq_of_idp_eq_con_inv (H : id = i ∘ q⁻¹) : q = i := (eq_of_con_inv_eq_idp H⁻¹)⁻¹
  definition eq_of_idp_eq_inv_con (H : id = q⁻¹ ∘ i) : q = i := (eq_of_inv_con_eq_idp H⁻¹)⁻¹
  definition inv_eq_of_idp_eq_con (H : id = h ∘ q) : q⁻¹ = h := (eq_inv_of_con_eq_idp' H⁻¹)⁻¹
  definition inv_eq_of_idp_eq_con' (H : id = q ∘ h) : q⁻¹ = h := (eq_inv_of_con_eq_idp H⁻¹)⁻¹
  end
  end iso

end morphism
