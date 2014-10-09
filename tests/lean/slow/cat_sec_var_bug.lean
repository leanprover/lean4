-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Floris van Doorn

-- category
import logic.eq logic.connectives
import data.unit data.sigma data.prod
import algebra.function
import logic.axioms.funext

open eq eq.ops

inductive category [class] (ob : Type) : Type :=
mk : Π (hom : ob → ob → Type) (comp : Π⦃a b c : ob⦄, hom b c → hom a b → hom a c)
           (id : Π {a : ob}, hom a a),
            (Π ⦃a b c d : ob⦄ {h : hom c d} {g : hom b c} {f : hom a b},
            comp h (comp g f) = comp (comp h g) f) →
           (Π ⦃a b : ob⦄ {f : hom a b}, comp id f = f) →
           (Π ⦃a b : ob⦄ {f : hom a b}, comp f id = f) →
            category ob

inductive Category : Type := mk : Π (ob : Type), category ob → Category

namespace category
  section
  parameters {ob : Type} {C : category ob}
  variables {a b c d : ob}

  definition hom : ob → ob → Type := rec (λ hom compose id assoc idr idl, hom) C
  definition compose : Π {a b c : ob}, hom b c → hom a b → hom a c :=
  rec (λ hom compose id assoc idr idl, compose) C

  definition id : Π {a : ob}, hom a a := rec (λ hom compose id assoc idr idl, id) C
  definition ID : Π (a : ob), hom a a := @id

  precedence `∘` : 60
  infixr `∘` := compose
  infixl `=>`:25 := hom

  variables {h : hom c d} {g : hom b c} {f : hom a b} {i : hom a a}

  theorem assoc : Π ⦃a b c d : ob⦄ (h : hom c d) (g : hom b c) (f : hom a b),
      h ∘ (g ∘ f) = (h ∘ g) ∘ f :=
  rec (λ hom comp id assoc idr idl, assoc) C

  theorem id_left  : Π ⦃a b : ob⦄ (f : hom a b), id ∘ f = f :=
  rec (λ hom comp id assoc idl idr, idl) C
  theorem id_right : Π ⦃a b : ob⦄ (f : hom a b), f ∘ id = f :=
  rec (λ hom comp id assoc idl idr, idr) C

  theorem id_compose (a : ob) : (ID a) ∘ id = id := !id_left

  theorem left_id_unique (H : Π{b} {f : hom b a}, i ∘ f = f) : i = id :=
  calc
    i = i ∘ id : symm !id_right
    ... = id : H

  theorem right_id_unique (H : Π{b} {f : hom a b}, f ∘ i = f) : i = id :=
  calc
    i = id ∘ i : eq.symm !id_left
    ... = id : H

  inductive is_section    [class] (f : hom a b) : Type := mk : ∀{g}, g ∘ f = id → is_section f
  inductive is_retraction [class] (f : hom a b) : Type := mk : ∀{g}, f ∘ g = id → is_retraction f
  inductive is_iso        [class] (f : hom a b) : Type := mk : ∀{g}, g ∘ f = id → f ∘ g = id → is_iso f

  definition retraction_of (f : hom a b) {H : is_section f} : hom b a :=
  is_section.rec (λg h, g) H
  definition section_of    (f : hom a b) {H : is_retraction f} : hom b a :=
  is_retraction.rec (λg h, g) H
  definition inverse       (f : hom a b) {H : is_iso f} : hom b a :=
  is_iso.rec (λg h1 h2, g) H

  postfix `⁻¹` := inverse

  theorem id_is_iso [instance] : is_iso (ID a) :=
  is_iso.mk !id_compose !id_compose

  theorem inverse_compose (f : hom a b) {H : is_iso f} : f⁻¹ ∘ f = id :=
  is_iso.rec (λg h1 h2, h1) H

  theorem compose_inverse (f : hom a b) {H : is_iso f} : f ∘ f⁻¹ = id :=
  is_iso.rec (λg h1 h2, h2) H

  theorem iso_imp_retraction [instance] (f : hom a b) {H : is_iso f} : is_section f :=
  is_section.mk !inverse_compose

  theorem iso_imp_section [instance] (f : hom a b) {H : is_iso f} : is_retraction f :=
  is_retraction.mk !compose_inverse

  theorem retraction_compose (f : hom a b) {H : is_section f} : retraction_of f ∘ f = id :=
  is_section.rec (λg h, h) H

  theorem compose_section (f : hom a b) {H : is_retraction f} : f ∘ section_of f = id :=
  is_retraction.rec (λg h, h) H

  theorem left_inverse_eq_right_inverse {f : hom a b} {g g' : hom b a}
      (Hl : g ∘ f = id) (Hr : f ∘ g' = id) : g = g' :=
  calc
    g = g ∘ id : symm !id_right
     ... = g ∘ f ∘ g' : {symm Hr}
     ... = (g ∘ f) ∘ g' : !assoc
     ... = id ∘ g' : {Hl}
     ... = g' : !id_left

  theorem section_eq_retraction {Hl : is_section f} {Hr : is_retraction f} :
      retraction_of f = section_of f :=
  left_inverse_eq_right_inverse !retraction_compose !compose_section

  theorem section_retraction_imp_iso {Hl : is_section f} {Hr : is_retraction f} : is_iso f :=
  is_iso.mk (subst section_eq_retraction !retraction_compose) !compose_section

  theorem inverse_unique (H H' : is_iso f) : @inverse _ _ f H = @inverse _ _ f H' :=
  left_inverse_eq_right_inverse !inverse_compose !compose_inverse

  theorem retraction_of_id : retraction_of (ID a) = id :=
  left_inverse_eq_right_inverse !retraction_compose !id_compose

  theorem section_of_id : section_of (ID a) = id :=
  symm (left_inverse_eq_right_inverse !id_compose !compose_section)

  theorem iso_of_id : ID a⁻¹ = id :=
  left_inverse_eq_right_inverse !inverse_compose !id_compose

  theorem composition_is_section [instance] {Hf : is_section f} {Hg : is_section g}
      : is_section (g ∘ f) :=
  is_section.mk
    (calc
      (retraction_of f ∘ retraction_of g) ∘ g ∘ f
            = retraction_of f ∘ retraction_of g ∘ g ∘ f : symm !assoc
        ... = retraction_of f ∘ (retraction_of g ∘ g) ∘ f : {!assoc}
        ... = retraction_of f ∘ id ∘ f : {!retraction_compose}
        ... = retraction_of f ∘ f : {!id_left}
        ... = id : !retraction_compose)

  theorem composition_is_retraction [instance] (Hf : is_retraction f) (Hg : is_retraction g)
      : is_retraction (g ∘ f) :=
  is_retraction.mk
    (calc
      (g ∘ f) ∘ section_of f ∘ section_of g = g ∘ f ∘ section_of f ∘ section_of g : symm !assoc
        ... = g ∘ (f ∘ section_of f) ∘ section_of g : {!assoc}
        ... = g ∘ id ∘ section_of g : {!compose_section}
        ... = g ∘ section_of g : {!id_left}
        ... = id : !compose_section)

  theorem composition_is_inverse [instance] (Hf : is_iso f) (Hg : is_iso g) : is_iso (g ∘ f) :=
  section_retraction_imp_iso

  definition mono (f : hom a b) : Prop := ∀⦃c⦄ {g h : hom c a}, f ∘ g = f ∘ h → g = h
  definition epi  (f : hom a b) : Prop := ∀⦃c⦄ {g h : hom b c}, g ∘ f = h ∘ f → g = h

  theorem section_is_mono (f : hom a b) {H : is_section f} : mono f :=
  λ C g h H,
  calc
    g = id ∘ g : symm !id_left
  ... = (retraction_of f ∘ f) ∘ g : {symm !retraction_compose}
  ... = retraction_of f ∘ f ∘ g : symm !assoc
  ... = retraction_of f ∘ f ∘ h : {H}
  ... = (retraction_of f ∘ f) ∘ h : !assoc
  ... = id ∘ h : {!retraction_compose}
  ... = h : !id_left

  theorem retraction_is_epi (f : hom a b) {H : is_retraction f} : epi f :=
  λ C g h H,
  calc
    g = g ∘ id : symm !id_right
  ... = g ∘ f ∘ section_of f : {symm !compose_section}
  ... = (g ∘ f) ∘ section_of f : !assoc
  ... = (h ∘ f) ∘ section_of f : {H}
  ... = h ∘ f ∘ section_of f : symm !assoc
  ... = h ∘ id : {!compose_section}
  ... = h : !id_right

  end

  section

  definition objects [coercion] (C : Category) : Type
  := Category.rec (fun c s, c) C

  definition category_instance [instance] (C : Category) : category (objects C)
  := Category.rec (fun c s, s) C

  end

end category

open category

inductive functor {obC obD : Type} (C : category obC) (D : category obD) : Type :=
mk : Π (obF : obC → obD) (homF : Π⦃a b : obC⦄, hom a b → hom (obF a) (obF b)),
    (Π ⦃a : obC⦄, homF (ID a) = ID (obF a)) →
    (Π ⦃a b c : obC⦄ {g : hom b c} {f : hom a b}, homF (g ∘ f) = homF g ∘ homF f) →
     functor C D

inductive Functor (C D : Category) : Type :=
mk : functor (category_instance C) (category_instance D) → Functor C D

infixl `⇒`:25 := functor

namespace functor
  section basic_functor
  variables {obC obD obE : Type} {C : category obC} {D : category obD} {E : category obE}
  definition object [coercion] (F : C ⇒ D) : obC → obD := rec (λ obF homF Hid Hcomp, obF) F

  definition morphism [coercion] (F : C ⇒ D) : Π{a b : obC}, hom a b → hom (F a) (F b) :=
  rec (λ obF homF Hid Hcomp, homF) F

  theorem respect_id (F : C ⇒ D) : Π (a : obC), F (ID a) = id :=
  rec (λ obF homF Hid Hcomp, Hid) F

  variable G : D ⇒ E
  check respect_id G

  theorem respect_comp (F : C ⇒ D) : Π ⦃a b c : obC⦄ (g : hom b c) (f : hom a b),
      F (g ∘ f) = F g ∘ F f :=
  rec (λ obF homF Hid Hcomp, Hcomp) F

  protected definition compose (G : D ⇒ E) (F : C ⇒ D) : C ⇒ E :=
  functor.mk
    (λx, G (F x))
    (λ a b f, G (F f))
    (λ a, calc
      G (F (ID a)) = G id : {respect_id F a}
               ... = id   : respect_id G (F a))
    (λ a b c g f, calc
      G (F (g ∘ f)) = G (F g ∘ F f)     : {respect_comp F g f}
                ... = G (F g) ∘ G (F f) : respect_comp G (F g) (F f))

  precedence `∘∘` : 60
  infixr `∘∘` := compose

  protected theorem assoc {obA obB obC obD : Type} {A : category obA} {B : category obB}
      {C : category obC} {D : category obD} (H : C ⇒ D) (G : B ⇒ C) (F : A ⇒ B) :
      H ∘∘ (G ∘∘ F) = (H ∘∘ G) ∘∘ F :=
  rfl

  -- later check whether we want implicit or explicit arguments here. For the moment, define both
  protected definition id {ob : Type} {C : category ob} : functor C C :=
  mk (λa, a) (λ a b f, f) (λ a, rfl) (λ a b c f g, rfl)
  protected definition ID {ob : Type} (C : category ob) : functor C C := id
  protected definition Id {C : Category} : Functor C C := Functor.mk id
  protected definition iD (C : Category) : Functor C C := Functor.mk id

  protected theorem id_left  (F : C ⇒ D) : id ∘∘ F = F := rec (λ obF homF idF compF, rfl) F
  protected theorem id_right (F : C ⇒ D) : F ∘∘ id = F := rec (λ obF homF idF compF, rfl) F

  end basic_functor

  section Functor
  variables {C₁ C₂ C₃ C₄: Category} --(G : Functor D E) (F : Functor C D)
  definition Functor_functor (F : Functor C₁ C₂) :
      functor (category_instance C₁) (category_instance C₂) :=
  Functor.rec (λ x, x) F

  protected definition Compose (G : Functor C₂ C₃) (F : Functor C₁ C₂) : Functor C₁ C₃ :=
  Functor.mk (compose (Functor_functor G) (Functor_functor F))

--  namespace Functor
  precedence `∘∘` : 60
  infixr `∘∘` := Compose
--  end Functor

  protected definition Assoc (H : Functor C₃ C₄) (G : Functor C₂ C₃) (F : Functor C₁ C₂)
    :  H ∘∘ (G ∘∘ F) = (H ∘∘ G) ∘∘ F :=
  rfl

  protected theorem Id_left (F : Functor C₁ C₂) : Id ∘∘ F = F :=
  Functor.rec (λ f, subst !id_left rfl) F

  protected theorem Id_right {F : Functor C₁ C₂} : F ∘∘ Id = F :=
  Functor.rec (λ f, subst !id_right rfl) F
  end Functor

end functor

open functor

inductive natural_transformation {obC obD : Type} {C : category obC} {D : category obD}
    (F G : functor C D) : Type :=
mk : Π (η : Π(a : obC), hom (object F a) (object G a)), (Π{a b : obC} (f : hom a b), morphism G f ∘ η a = η b ∘ morphism F f)
 → natural_transformation F G

-- inductive Natural_transformation {C D : Category} (F G : Functor C D) : Type :=
-- mk : natural_transformation (Functor_functor F) (Functor_functor G) → Natural_transformation F G

infixl `==>`:25 := natural_transformation

namespace natural_transformation
  section
  parameters {obC obD : Type} {C : category obC} {D : category obD} {F G : C ⇒ D}

  definition natural_map [coercion] (η : F ==> G) :
      Π(a : obC), hom (object F a) (object G a) :=
  rec (λ x y, x) η

  definition naturality (η : F ==> G) :
      Π{a b : obC} (f : hom a b), morphism G f ∘ η a = η b ∘ morphism F f :=
  rec (λ x y, y) η
  end

  section
  parameters {obC obD : Type} {C : category obC} {D : category obD} {F G H : C ⇒ D}
  protected definition compose (η : G ==> H) (θ : F ==> G) : F ==> H :=
  natural_transformation.mk
    (λ a, η a ∘ θ a)
    (λ a b f,
      calc
        morphism H f ∘ (η a ∘ θ a) = (morphism H f ∘ η a) ∘ θ a : !assoc
          ... = (η b ∘ morphism G f) ∘ θ a : {naturality η f}
          ... = η b ∘ (morphism G f ∘ θ a) : symm !assoc
          ... = η b ∘ (θ b ∘ morphism F f) : {naturality θ f}
          ... = (η b ∘ θ b) ∘ morphism F f : !assoc)
  end
  precedence `∘n` : 60
  infixr `∘n` := compose
end natural_transformation
