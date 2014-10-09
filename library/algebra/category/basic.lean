-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Floris van Doorn

import logic.axioms.funext

open eq eq.ops

inductive category [class] (ob : Type) : Type :=
mk : Π (hom : ob → ob → Type) 
       (comp : Π⦃a b c : ob⦄, hom b c → hom a b → hom a c)
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

  definition hom [reducible] : ob → ob → Type := rec (λ hom compose id assoc idr idl, hom) C
  -- note: needs to be reducible to typecheck composition in opposite category
  definition compose [reducible] : Π {a b c : ob}, hom b c → hom a b → hom a c :=
  rec (λ hom compose id assoc idr idl, compose) C

  definition id [reducible] : Π {a : ob}, hom a a := rec (λ hom compose id assoc idr idl, id) C
  definition ID [reducible] : Π (a : ob), hom a a := @id

  infixr `∘`:60 := compose
  infixl `⟶`:25 := hom -- input ⟶ using \-->

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

  infixr `∘∘`:60 := compose

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
  definition Functor_functor {C₁ C₂ : Category} (F : Functor C₁ C₂) : --remove params
      functor (category_instance C₁) (category_instance C₂) :=
  Functor.rec (λ x, x) F

  protected definition Compose (G : Functor C₂ C₃) (F : Functor C₁ C₂) : Functor C₁ C₃ :=
  Functor.mk (compose (Functor_functor G) (Functor_functor F))

--  namespace Functor
  infixr `∘∘`:60 := Compose
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

infixl `⟹`:25 := natural_transformation

namespace natural_transformation
  section
  parameters {obC obD : Type} {C : category obC} {D : category obD} {F G : C ⇒ D}

  definition natural_map [coercion] (η : F ⟹ G) :
      Π(a : obC), hom (object F a) (object G a) :=
  rec (λ x y, x) η

  definition naturality (η : F ⟹ G) :
      Π{a b : obC} (f : hom a b), morphism G f ∘ η a = η b ∘ morphism F f :=
  rec (λ x y, y) η
  end

  section
  parameters {obC obD : Type} {C : category obC} {D : category obD} {F G H : C ⇒ D}
  protected definition compose (η : G ⟹ H) (θ : F ⟹ G) : F ⟹ H :=
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
  section
  variables {obC obD : Type} {C : category obC} {D : category obD} {F₁ F₂ F₃ F₄ : C ⇒ D}
  protected theorem assoc (η₃ : F₃ ⟹ F₄) (η₂ : F₂ ⟹ F₃) (η₁ : F₁ ⟹ F₂) : 
      η₃ ∘n (η₂ ∘n η₁) = (η₃ ∘n η₂) ∘n η₁ :=
  congr_arg2_dep mk (funext (take x, !assoc)) !proof_irrel

  --TODO: check whether some of the below identities are superfluous
  protected definition id {obC obD : Type} {C : category obC} {D : category obD} {F : C ⇒ D}
      : natural_transformation F F :=
  mk (λa, id) (λa b f, !id_right ⬝ symm !id_left)
  protected definition ID {obC obD : Type} {C : category obC} {D : category obD} (F : C ⇒ D)
      : natural_transformation F F := id
  -- protected definition Id {C D : Category} {F : Functor C D} : Natural_transformation F F :=
  -- Natural_transformation.mk id
  -- protected definition iD {C D : Category} (F : Functor C D) : Natural_transformation F F :=
  -- Natural_transformation.mk id

  protected theorem id_left (η : F₁ ⟹ F₂) : natural_transformation.compose id η = η :=
  rec (λf H, congr_arg2_dep mk (funext (take x, !id_left)) !proof_irrel) η

  protected theorem id_right (η : F₁ ⟹ F₂) : natural_transformation.compose η id = η :=
  rec (λf H, congr_arg2_dep mk (funext (take x, !id_right)) !proof_irrel) η

  end
end natural_transformation


