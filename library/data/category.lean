-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Floris van Doorn

-- category
import logic.core.eq logic.core.connectives
import data.unit data.sigma data.prod
import struc.function

open eq

inductive category [class] (ob : Type) : Type :=
mk : Π (mor : ob → ob → Type) (comp : Π{A B C : ob}, mor B C → mor A B → mor A C)
           (id : Π {A : ob}, mor A A),
            (Π {A B C D : ob} {f : mor A B} {g : mor B C} {h : mor C D},
            comp h (comp g f) = comp (comp h g) f) →
           (Π {A B : ob} {f : mor A B}, comp f id = f) →
           (Π {A B : ob} {f : mor A B}, comp id f = f) →
            category ob

namespace category
  precedence `∘` : 60

  section
  parameters {ob : Type} {Cat : category ob} {A B C D : ob}


  definition mor : ob → ob → Type := rec (λ mor compose id assoc idr idl, mor) Cat
  definition compose : Π {A B C : ob}, mor B C → mor A B → mor A C :=
  rec (λ mor compose id assoc idr idl, compose) Cat
  definition id : Π {A : ob}, mor A A :=
  rec (λ mor compose id assoc idr idl, id) Cat
  abbreviation ID (A : ob) : mor A A := @id A

  infixr `∘` := compose

  theorem assoc : Π {A B C D : ob} {f : mor A B} {g : mor B C} {h : mor C D},
                h ∘ (g ∘ f) = (h ∘ g) ∘ f :=
  rec (λ mor comp id assoc idr idl, assoc) Cat

  theorem id_right : Π {A B : ob} {f : mor A B}, f ∘ id = f :=
  rec (λ mor comp id assoc idr idl, idr) Cat
  theorem id_left  : Π {A B : ob} {f : mor A B}, id ∘ f = f :=
  rec (λ mor comp id assoc idr idl, idl) Cat

  theorem id_compose : (ID A) ∘ id = id :=
  id_left

  theorem left_id_unique (i : mor A A) (H : Π{B} {f : mor B A}, i ∘ f = f) : i = id :=
  calc
    i = i ∘ id : eq.symm id_right
    ... = id : H

  theorem right_id_unique (i : mor A A) (H : Π{B} {f : mor A B}, f ∘ i = f) : i = id :=
  calc
    i = id ∘ i : eq.symm id_left
    ... = id : H

  inductive is_section {A B : ob} (f : mor A B) : Type :=
  mk : ∀{g}, g ∘ f = id → is_section f
  inductive is_retraction {A B : ob} (f : mor A B) : Type :=
  mk : ∀{g}, f ∘ g = id → is_retraction f
  inductive is_iso {A B : ob} (f : mor A B) : Type :=
  mk : ∀{g}, g ∘ f = id → f ∘ g = id → is_iso f

  definition retraction_of {A B : ob} (f : mor A B) {H : is_section f} : mor B A :=
  is_section.rec (λg h, g) H
  definition section_of {A B : ob} (f : mor A B) {H : is_retraction f} : mor B A :=
  is_retraction.rec (λg h, g) H
  definition inverse {A B : ob} (f : mor A B) {H : is_iso f} : mor B A :=
  is_iso.rec (λg h1 h2, g) H

  postfix `⁻¹` := inverse

  theorem id_is_iso [instance] : is_iso (ID A) :=
  is_iso.mk id_compose id_compose

  theorem inverse_compose {A B : ob} {f : mor A B} {H : is_iso f} : f⁻¹ ∘ f = id :=
  is_iso.rec (λg h1 h2, h1) H

  theorem compose_inverse {A B : ob} {f : mor A B} {H : is_iso f} : f ∘ f⁻¹ = id :=
  is_iso.rec (λg h1 h2, h2) H

  theorem iso_imp_retraction [instance] {A B : ob} (f : mor A B) {H : is_iso f} : is_section f :=
  is_section.mk inverse_compose

  theorem iso_imp_section [instance] {A B : ob} (f : mor A B) {H : is_iso f} : is_retraction f :=
  is_retraction.mk compose_inverse

  theorem retraction_compose {A B : ob} {f : mor A B} {H : is_section f} :
      retraction_of f ∘ f = id :=
  is_section.rec (λg h, h) H

  theorem compose_section {A B : ob} {f : mor A B} {H : is_retraction f} :
      f ∘ section_of f = id :=
  is_retraction.rec (λg h, h) H

  theorem left_inverse_eq_right_inverse {A B : ob} {f : mor A B} {g g' : mor B A}
      (Hl : g ∘ f = id) (Hr : f ∘ g' = id) : g = g' :=
  calc
    g = g ∘ id : symm id_right
     ... = g ∘ f ∘ g' : {symm Hr}
     ... = (g ∘ f) ∘ g' : assoc
     ... = id ∘ g' : {Hl}
     ... = g' : id_left

  theorem section_eq_retraction {A B : ob} {f : mor A B}
      (Hl : is_section f) (Hr : is_retraction f) : retraction_of f = section_of f :=
  left_inverse_eq_right_inverse retraction_compose compose_section

  theorem section_retraction_imp_iso {A B : ob} {f : mor A B}
      (Hl : is_section f) (Hr : is_retraction f) : is_iso f :=
  is_iso.mk (subst (section_eq_retraction Hl Hr) retraction_compose) compose_section

  -- theorem inverse_unique {A B : ob} {f : mor A B} (H H' : is_iso f)
  --         : @inverse _ _ f H = @inverse _ _ f H' :=
  -- left_inverse_eq_right_inverse inverse_compose compose_inverse

  theorem retraction_of_id {A : ob} : retraction_of (ID A) = id :=
  left_inverse_eq_right_inverse retraction_compose id_compose

  theorem section_of_id {A : ob} : section_of (ID A) = id :=
  symm (left_inverse_eq_right_inverse id_compose compose_section)

  theorem iso_of_id {A : ob} : ID A⁻¹ = id :=
  left_inverse_eq_right_inverse inverse_compose id_compose

  theorem composition_is_section [instance] {f : mor A B} {g : mor B C} 
      (Hf : is_section f) (Hg : is_section g) : is_section (g ∘ f) :=
  is_section.mk
    (calc
      (retraction_of f ∘ retraction_of g) ∘ g ∘ f 
            = retraction_of f ∘ retraction_of g ∘ g ∘ f : symm assoc
        ... = retraction_of f ∘ (retraction_of g ∘ g) ∘ f : {assoc}
        ... = retraction_of f ∘ id ∘ f : {retraction_compose}
        ... = retraction_of f ∘ f : {id_left}
        ... = id : retraction_compose)

  theorem composition_is_retraction [instance] {f : mor A B} {g : mor B C} 
      (Hf : is_retraction f) (Hg : is_retraction g) : is_retraction (g ∘ f) :=
  is_retraction.mk
    (calc
      (g ∘ f) ∘ section_of f ∘ section_of g = g ∘ f ∘ section_of f ∘ section_of g : symm assoc
        ... = g ∘ (f ∘ section_of f) ∘ section_of g : {assoc}
        ... = g ∘ id ∘ section_of g : {compose_section}
        ... = g ∘ section_of g : {id_left}
        ... = id : compose_section)

  theorem composition_is_inverse [instance] {f : mor A B} {g : mor B C} 
      (Hf : is_iso f) (Hg : is_iso g) : is_iso (g ∘ f) :=
  section_retraction_imp_iso _ _

  definition mono {A B : ob} (f : mor A B) : Prop :=
  ∀⦃C⦄ {g h : mor C A}, f ∘ g = f ∘ h → g = h
  definition epi  {A B : ob} (f : mor A B) : Prop :=
  ∀⦃C⦄ {g h : mor B C}, g ∘ f = h ∘ f → g = h

  theorem section_is_mono {f : mor A B} (H : is_section f) : mono f :=
  λ C g h H, 
  calc
    g = id ∘ g : symm id_left
  ... = (retraction_of f ∘ f) ∘ g : {symm retraction_compose}
  ... = retraction_of f ∘ f ∘ g : symm assoc
  ... = retraction_of f ∘ f ∘ h : {H}
  ... = (retraction_of f ∘ f) ∘ h : assoc
  ... = id ∘ h : {retraction_compose}
  ... = h : id_left

  theorem retraction_is_epi {f : mor A B} (H : is_retraction f) : epi f :=
  λ C g h H, 
  calc
    g = g ∘ id : symm id_right
  ... = g ∘ f ∘ section_of f : {symm compose_section}
  ... = (g ∘ f) ∘ section_of f : assoc
  ... = (h ∘ f) ∘ section_of f : {H}
  ... = h ∘ f ∘ section_of f : symm assoc
  ... = h ∘ id : {compose_section}
  ... = h : id_right

  end
  infixr `∘` := compose
  postfix `⁻¹` := inverse

  section
  open unit
  definition one [instance] : category unit :=
  category.mk (λa b, unit) (λ a b c f g, star) (λ a, star) (λ a b c d f g h, unit.equal _ _)
    (λ a b f, unit.equal _ _) (λ a b f, unit.equal _ _)
  end

  section
  parameter {ob : Type}
  definition opposite [instance] (C : category ob) : category ob :=
  category.mk (λa b, mor b a) (λ a b c f g, g ∘ f) (λ a, id) (λ a b c d f g h, symm assoc)
    (λ a b f, id_left) (λ a b f, id_right)
  precedence `∘op` : 60
  infixr `∘op` := @compose _ (opposite _) _ _ _

  -- parameters {C : category ob} {a b c : ob} {f : @mor ob C a b} {g : @mor ob C b c}
  -- check g ∘ f
  -- check f ∘op g
  -- check f ∘op g = g ∘ f
  
  -- theorem compose_op : f ∘op g = g ∘ f := 
  -- rfl
  -- theorem compose_op {C : category ob} {a b c : ob} {f : @mor ob C a b} {g : @mor ob C b c} : f ∘op g = g ∘ f := 
  -- rfl
  -- theorem op_op {C : category ob} : opposite (opposite C) = C :=
  -- rec (λ mor comp id assoc idl idr, sorry) C
  end  

  section
  --need extensionality
  -- definition type_cat : category Type :=
  -- mk (λA B, A → B) (λ a b c f g, function.compose f g) (λ a, function.id) (λ a b c d f g h, sorry)
  --   (λ a b f, sorry) (λ a b f, sorry)
  end

end category

open category

inductive functor {obC obD : Type} (C : category obC) (D : category obD) : Type :=
mk : Π (obF : obC → obD) (morF : Π{A B : obC}, mor A B → mor (obF A) (obF B)),
    (Π {A : obC}, morF (ID A) = ID (obF A)) →
    (Π {A B C : obC} {f : mor A B} {g : mor B C}, morF (g ∘ f) = morF g ∘ morF f) →
     @functor obC obD C D

namespace functor
  section
  parameters {obC obD : Type} {C : category obC} {D : category obD} (F : functor C D)
  definition object : obC → obD := rec (λ obF morF Hid Hcomp, obF) F
  definition morphism : Π{A B : obC}, mor A B → mor (object A) (object B) :=
  rec (λ obF morF Hid Hcomp, morF) F
  theorem respect_id : Π {A : obC}, morphism (ID A) = ID (object A) :=
  rec (λ obF morF Hid Hcomp, Hid) F
  theorem respect_comp : Π {a b c : obC} {f : mor a b} {g : mor b c},
      morphism (g ∘ f) = morphism g ∘ morphism f :=
  rec (λ obF morF Hid Hcomp, Hcomp) F
  end
end functor
