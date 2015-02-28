/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.category.morphism
Author: Floris van Doorn, Jakob von Raumer
-/

import algebra.precategory.basic

open eq category sigma sigma.ops equiv is_equiv is_trunc

namespace morphism
  structure split_mono [class] {ob : Type} [C : precategory ob] {a b : ob} (f : a ⟶ b) :=
    {retraction_of : b ⟶ a}
    (retraction_comp : retraction_of ∘ f = id)
  structure split_epi [class] {ob : Type} [C : precategory ob] {a b : ob} (f : a ⟶ b) :=
    {section_of : b ⟶ a}
    (comp_section : f ∘ section_of = id)
  structure is_iso [class] {ob : Type} [C : precategory ob] {a b : ob} (f : a ⟶ b) :=
    {inverse : b ⟶ a}
    (left_inverse : inverse ∘ f = id)
    (right_inverse : f ∘ inverse = id)

  attribute is_iso [multiple-instances]
  open split_mono split_epi is_iso
  definition retraction_of [reducible] := @split_mono.retraction_of
  definition retraction_comp [reducible] := @split_mono.retraction_comp
  definition section_of [reducible] := @split_epi.section_of
  definition comp_section [reducible] := @split_epi.comp_section
  definition inverse [reducible] := @is_iso.inverse
  definition left_inverse [reducible] := @is_iso.left_inverse
  definition right_inverse [reducible] := @is_iso.right_inverse
  postfix `⁻¹` := inverse
  --a second notation for the inverse, which is not overloaded
  postfix [parsing-only] `⁻¹ʰ`:std.prec.max_plus := inverse

  variables {ob : Type} [C : precategory ob]
  variables {a b c : ob} {g : b ⟶ c} {f : a ⟶ b} {h : b ⟶ a}
  include C

  definition iso_imp_retraction [instance] [priority 300] [reducible]
    (f : a ⟶ b) [H : is_iso f] : split_mono f :=
  split_mono.mk !left_inverse

  definition iso_imp_section [instance] [priority 300] [reducible]
    (f : a ⟶ b) [H : is_iso f] : split_epi f :=
  split_epi.mk !right_inverse

  definition is_iso_id [instance] [priority 500] (a : ob) : is_iso (ID a) :=
  is_iso.mk !id_comp !id_comp

  definition is_iso_inverse [instance] [priority 200] (f : a ⟶ b) [H : is_iso f] : is_iso f⁻¹ :=
  is_iso.mk !right_inverse !left_inverse

  definition left_inverse_eq_right_inverse {f : a ⟶ b} {g g' : hom b a}
      (Hl : g ∘ f = id) (Hr : f ∘ g' = id) : g = g' :=
  by rewrite [-(id_right g), -Hr, assoc, Hl, id_left]

  definition retraction_eq [H : split_mono f] (H2 : f ∘ h = id) : retraction_of f = h :=
  left_inverse_eq_right_inverse !retraction_comp H2

  definition section_eq [H : split_epi f] (H2 : h ∘ f = id) : section_of f = h :=
  (left_inverse_eq_right_inverse H2 !comp_section)⁻¹

  definition inverse_eq_right [H : is_iso f] (H2 : f ∘ h = id) : f⁻¹ = h :=
  left_inverse_eq_right_inverse !left_inverse H2

  definition inverse_eq_left [H : is_iso f] (H2 : h ∘ f = id) : f⁻¹ = h :=
  (left_inverse_eq_right_inverse H2 !right_inverse)⁻¹

  definition retraction_eq_section (f : a ⟶ b) [Hl : split_mono f] [Hr : split_epi f] :
      retraction_of f = section_of f :=
  retraction_eq !comp_section

  definition iso_of_split_epi_of_split_mono (f : a ⟶ b) [Hl : split_mono f] [Hr : split_epi f]
    : is_iso f :=
  is_iso.mk ((retraction_eq_section f) ▹ (retraction_comp f)) (comp_section f)

  definition inverse_unique (H H' : is_iso f) : @inverse _ _ _ _ f H = @inverse _ _ _ _ f H' :=
  inverse_eq_left !left_inverse

  definition inverse_involutive (f : a ⟶ b) [H : is_iso f] : (f⁻¹)⁻¹ = f :=
  inverse_eq_right !left_inverse

  definition retraction_id (a : ob) : retraction_of (ID a) = id :=
  retraction_eq !id_comp

  definition section_id (a : ob) : section_of (ID a) = id :=
  section_eq !id_comp

  definition id_inverse (a : ob) [H : is_iso (ID a)] : (ID a)⁻¹ = id :=
  inverse_eq_left !id_comp

  definition split_mono_comp [instance] [priority 150] (g : b ⟶ c) (f : a ⟶ b)
    [Hf : split_mono f] [Hg : split_mono g] : split_mono (g ∘ f) :=
  split_mono.mk
    (show (retraction_of f ∘ retraction_of g) ∘ g ∘ f = id,
     by rewrite [-assoc, assoc _ g f, retraction_comp, id_left, retraction_comp])

  definition split_epi_comp [instance] [priority 150] (g : b ⟶ c) (f : a ⟶ b)
    [Hf : split_epi f] [Hg : split_epi g] : split_epi (g ∘ f) :=
  split_epi.mk
    (show (g ∘ f) ∘ section_of f ∘ section_of g = id,
     by rewrite [-assoc, {f ∘ _}assoc, comp_section, id_left, comp_section])

  definition iso_comp [instance] [priority 150] (g : b ⟶ c) (f : a ⟶ b)
    [Hf : is_iso f] [Hg : is_iso g] : is_iso (g ∘ f) :=
  !iso_of_split_epi_of_split_mono

  structure isomorphic (a b : ob) :=
    (to_fun : hom a b)
    [struct : is_iso to_fun]

  infix `≅`:50 := morphism.isomorphic
  attribute isomorphic.struct [instance] [priority 400]

  namespace isomorphic
    attribute to_fun [coercion]

    protected definition refl (a : ob) : a ≅ a :=
    mk (ID a)

    protected definition symm ⦃a b : ob⦄ (H : a ≅ b) : b ≅ a :=
    mk (to_fun H)⁻¹

    protected definition trans ⦃a b c : ob⦄ (H1 : a ≅ b) (H2 : b ≅ c) : a ≅ c :=
    mk (to_fun H2 ∘ to_fun H1)

  end isomorphic

  structure mono [class] (f : a ⟶ b) :=
    (elim : ∀c (g h : hom c a), f ∘ g = f ∘ h → g = h)
  structure epi  [class] (f : a ⟶ b) :=
    (elim : ∀c (g h : hom b c), g ∘ f = h ∘ f → g = h)

  definition mono_of_split_mono [instance] (f : a ⟶ b) [H : split_mono f] : mono f :=
  mono.mk
    (λ c g h H,
      calc
        g = id ∘ g                    : by rewrite id_left
      ... = (retraction_of f ∘ f) ∘ g : by rewrite -retraction_comp
      ... = (retraction_of f ∘ f) ∘ h : by rewrite [-assoc, H, -assoc]
      ... = id ∘ h                    : by rewrite retraction_comp
      ... = h                         : by rewrite id_left)

  definition epi_of_split_epi [instance] (f : a ⟶ b) [H : split_epi f] : epi f :=
  epi.mk
    (λ c g h H,
      calc
        g = g ∘ id                 : by rewrite id_right
      ... = g ∘ f ∘ section_of f   : by rewrite -comp_section
      ... = h ∘ f ∘ section_of f   : by rewrite [assoc, H, -assoc]
      ... = h ∘ id                 : by rewrite comp_section
      ... = h                      : by rewrite id_right)

  definition mono_comp [instance] (g : b ⟶ c) (f : a ⟶ b) [Hf : mono f] [Hg : mono g]
    : mono (g ∘ f) :=
  mono.mk
    (λ d h₁ h₂ H,
    have H2 : g ∘ (f ∘ h₁) = g ∘ (f ∘ h₂),
    begin
      rewrite *assoc, exact H
    end,
    !mono.elim (!mono.elim H2))

  definition epi_comp  [instance] (g : b ⟶ c) (f : a ⟶ b) [Hf : epi f] [Hg : epi g]
    : epi  (g ∘ f) :=
  epi.mk
    (λ d h₁ h₂ H,
    have H2 : (h₁ ∘ g) ∘ f = (h₂ ∘ g) ∘ f,
    begin
      rewrite -*assoc, exact H
    end,
    !epi.elim (!epi.elim H2))

end morphism

namespace morphism
  /-
  rewrite lemmas for inverses, modified from
  https://github.com/JasonGross/HoTT-categories/blob/master/theories/Categories/Category/Morphisms.v
  -/
  namespace to_fun
  section
  variables {ob : Type} [C : precategory ob] include C
  variables {a b c d : ob}                         (f : b ⟶ a)
                           (r : c ⟶ d) (q : b ⟶ c) (p : a ⟶ b)
                           (g : d ⟶ c)
  variable [Hq : is_iso q] include Hq
  definition comp.right_inverse : q ∘ q⁻¹ = id := !right_inverse
  definition comp.left_inverse : q⁻¹ ∘ q = id := !left_inverse
  definition inverse_comp_cancel_left : q⁻¹ ∘ (q ∘ p) = p :=
   by rewrite [assoc, left_inverse, id_left]
  definition comp_inverse_cancel_left : q ∘ (q⁻¹ ∘ g) = g :=
   by rewrite [assoc, right_inverse, id_left]
  definition comp_inverse_cancel_right : (r ∘ q) ∘ q⁻¹ = r :=
  by rewrite [-assoc, right_inverse, id_right]
  definition inverse_comp_cancel_right : (f ∘ q⁻¹) ∘ q = f :=
  by rewrite [-assoc, left_inverse, id_right]

  definition right_inverse [Hp : is_iso p] [Hpq : is_iso (q ∘ p)] : (q ∘ p)⁻¹ʰ = p⁻¹ʰ ∘ q⁻¹ʰ :=
  inverse_eq_left
    (show (p⁻¹ʰ ∘ q⁻¹ʰ) ∘ q ∘ p = id, from
     by rewrite [-assoc, inverse_comp_cancel_left, left_inverse])

  definition inverse_comp_inverse_left [H' : is_iso g] : (q⁻¹ ∘ g)⁻¹ = g⁻¹ ∘ q :=
  inverse_involutive q ▹ right_inverse q⁻¹ g

  definition inverse_comp_inverse_right [H' : is_iso f] : (q ∘ f⁻¹)⁻¹ = f ∘ q⁻¹ :=
  inverse_involutive f ▹ right_inverse q f⁻¹

  definition inverse_comp_inverse_inverse [H' : is_iso r] : (q⁻¹ ∘ r⁻¹)⁻¹ = r ∘ q :=
  inverse_involutive r ▹ inverse_comp_inverse_left q r⁻¹
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

  definition comp_eq_of_eq_inverse_comp (H : y = q⁻¹ ∘ g) : q ∘ y = g :=
  H⁻¹ ▹ comp_inverse_cancel_left q g
  definition comp_eq_of_eq_comp_inverse (H : w = f ∘ q⁻¹) : w ∘ q = f :=
  H⁻¹ ▹ inverse_comp_cancel_right f q
  definition inverse_comp_eq_of_eq_comp (H : z = q ∘ p) : q⁻¹ ∘ z = p :=
  H⁻¹ ▹ inverse_comp_cancel_left q p
  definition comp_inverse_eq_of_eq_comp (H : x = r ∘ q) : x ∘ q⁻¹ = r :=
  H⁻¹ ▹ comp_inverse_cancel_right r q
  definition eq_comp_of_inverse_comp_eq (H : q⁻¹ ∘ g = y) : g = q ∘ y :=
  (comp_eq_of_eq_inverse_comp H⁻¹)⁻¹
  definition eq_comp_of_comp_inverse_eq (H : f ∘ q⁻¹ = w) : f = w ∘ q :=
  (comp_eq_of_eq_comp_inverse H⁻¹)⁻¹
  definition eq_inverse_comp_of_comp_eq (H : q ∘ p = z) : p = q⁻¹ ∘ z :=
  (inverse_comp_eq_of_eq_comp H⁻¹)⁻¹
  definition eq_comp_inverse_of_comp_eq (H : r ∘ q = x) : r = x ∘ q⁻¹ :=
  (comp_inverse_eq_of_eq_comp H⁻¹)⁻¹
  definition eq_inverse_of_comp_eq_id' (H : h ∘ q = id) : h = q⁻¹ := (inverse_eq_left H)⁻¹
  definition eq_inverse_of_comp_eq_id (H : q ∘ h = id) : h = q⁻¹ := (inverse_eq_right H)⁻¹
  definition eq_of_comp_inverse_eq_id (H : i ∘ q⁻¹ = id) : i = q :=
  eq_inverse_of_comp_eq_id' H ⬝ inverse_involutive q
  definition eq_of_inverse_comp_eq_id (H : q⁻¹ ∘ i = id) : i = q :=
  eq_inverse_of_comp_eq_id H ⬝ inverse_involutive q
  definition eq_of_id_eq_comp_inverse (H : id = i ∘ q⁻¹) : q = i := (eq_of_comp_inverse_eq_id H⁻¹)⁻¹
  definition eq_of_id_eq_inverse_comp (H : id = q⁻¹ ∘ i) : q = i := (eq_of_inverse_comp_eq_id H⁻¹)⁻¹
  definition inverse_eq_of_id_eq_comp (H : id = h ∘ q) : q⁻¹ = h :=
  (eq_inverse_of_comp_eq_id' H⁻¹)⁻¹
  definition inverse_eq_of_id_eq_comp' (H : id = q ∘ h) : q⁻¹ = h :=
  (eq_inverse_of_comp_eq_id H⁻¹)⁻¹
  end
  end to_fun

end morphism
