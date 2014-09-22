-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Floris van Doorn

-- category
import logic.core.eq logic.core.connectives
import data.unit data.sigma data.prod
import algebra.function
import logic.axioms.funext

open eq

inductive category [class] (ob : Type) : Type :=
mk : Π (mor : ob → ob → Type) (comp : Π⦃A B C : ob⦄, mor B C → mor A B → mor A C)
           (id : Π {A : ob}, mor A A),
            (Π ⦃A B C D : ob⦄ {h : mor C D} {g : mor B C} {f : mor A B},
            comp h (comp g f) = comp (comp h g) f) →
           (Π ⦃A B : ob⦄ {f : mor A B}, comp id f = f) →
           (Π ⦃A B : ob⦄ {f : mor A B}, comp f id = f) →
            category ob

inductive Category : Type :=
mk : Π (A : Type), category A → Category

namespace category

  section
  parameters {ob : Type} {Cat : category ob} {A B C D : ob}

  definition mor : ob → ob → Type := rec (λ mor compose id assoc idr idl, mor) Cat
  definition compose : Π {A B C : ob}, mor B C → mor A B → mor A C :=
  rec (λ mor compose id assoc idr idl, compose) Cat

  definition id : Π {A : ob}, mor A A :=
  rec (λ mor compose id assoc idr idl, id) Cat
  definition ID (A : ob) : mor A A := @id A

  precedence `∘` : 60
  infixr `∘` := compose

  theorem assoc : Π {A B C D : ob} {h : mor C D} {g : mor B C} {f : mor A B},
                h ∘ (g ∘ f) = (h ∘ g) ∘ f :=
  rec (λ mor comp id assoc idr idl, assoc) Cat

  theorem id_left  : Π {A B : ob} {f : mor A B}, id ∘ f = f :=
  rec (λ mor comp id assoc idl idr, idl) Cat
  theorem id_right : Π {A B : ob} {f : mor A B}, f ∘ id = f :=
  rec (λ mor comp id assoc idl idr, idr) Cat

  theorem id_compose {A : ob} : (ID A) ∘ id = id :=
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

  theorem inverse_unique {A B : ob} {f : mor A B} (H H' : is_iso f)
          : @inverse _ _ f H = @inverse _ _ f H' :=
  left_inverse_eq_right_inverse inverse_compose compose_inverse

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

  section

  definition objects [coercion] (C : Category) : Type
  := Category.rec (fun c s, c) C

  definition category_instance [instance] (C : Category) : category (objects C)
  := Category.rec (fun c s, s) C

  end

  section
  open unit
  definition one [instance] : category unit :=
  category.mk (λa b, unit) (λ a b c f g, star) (λ a, star) (λ a b c d f g h, unit.equal _ _)
    (λ a b f, unit.equal _ _) (λ a b f, unit.equal _ _)
  end

  section
  parameter {ob : Type}
  definition opposite (C : category ob) : category ob :=
  category.mk (λa b, mor b a) (λ a b c f g, g ∘ f) (λ a, id) (λ a b c d f g h, symm assoc)
    (λ a b f, id_right) (λ a b f, id_left)
  precedence `∘op` : 60
  infixr `∘op` := @compose _ (opposite _) _ _ _

  parameters {C : category ob} {a b c : ob}

  theorem compose_op {f : @mor ob C a b} {g : mor b c} : f ∘op g = g ∘ f :=
  rfl

  theorem op_op {C : category ob} : opposite (opposite C) = C :=
  rec (λ mor comp id assoc idl idr, rfl) C

  end

  definition Opposite (C : Category) : Category :=
  Category.mk (objects C) (opposite (category_instance C))


  section
  --need extensionality
  -- definition type_cat : category Type :=
  -- mk (λA B, A → B) (λ a b c f g, function.compose f g) (λ a, function.id) (λ a b c d f g h, sorry)
  --   (λ a b f, sorry) (λ a b f, sorry)
  end

end category

open category

inductive functor {obC obD : Type} (C : category obC) (D : category obD) : Type :=
mk : Π (obF : obC → obD) (morF : Π⦃A B : obC⦄, mor A B → mor (obF A) (obF B)),
    (Π ⦃A : obC⦄, morF (ID A) = ID (obF A)) →
    (Π ⦃A B C : obC⦄ {f : mor A B} {g : mor B C}, morF (g ∘ f) = morF g ∘ morF f) →
     functor C D

inductive Functor (C D : Category) : Type :=
mk : functor (category_instance C) (category_instance D) → Functor C D

infixl `⇒`:25 := functor

namespace functor
  section basic_functor
  parameters {obC obD : Type} {C : category obC} {D : category obD}
  definition object [coercion] (F : C ⇒ D) : obC → obD := rec (λ obF morF Hid Hcomp, obF) F

  definition morphism [coercion] (F : C ⇒ D) : Π{A B : obC}, mor A B → mor (F A) (F B) :=
  rec (λ obF morF Hid Hcomp, morF) F

  theorem respect_id (F : C ⇒ D) : Π {A : obC}, F (ID A) = ID (F A) :=
  rec (λ obF morF Hid Hcomp, Hid) F

  theorem respect_comp (F : C ⇒ D) : Π {a b c : obC} {f : mor a b} {g : mor b c},
      F (g ∘ f) = F g ∘ F f :=
  rec (λ obF morF Hid Hcomp, Hcomp) F
  end basic_functor

  section category_functor

  definition compose {obC obD obE : Type} {C : category obC} {D : category obD} {E : category obE}
      (G : D ⇒ E) (F : C ⇒ D) : C ⇒ E :=
  functor.mk C E
    (λx, G (F x))
    (λ a b f, G (F f))
    (λ a, calc
      G (F (ID a)) = G id : {respect_id F}
               ... = id   : respect_id G)
    (λ a b c f g, calc
      G (F (g ∘ f)) = G (F g ∘ F f)     : {respect_comp F}
                ... = G (F g) ∘ G (F f) : respect_comp G)

  precedence `∘∘` : 60
  infixr `∘∘` := compose

  -- theorem congr_functor {obC obD : Type} {C : category obC} {D : category obD} {o : obC → obD}
  --     {m m' : Π⦃A B : obC⦄, mor A B → mor (o A) (o B)} {i i' c c'}
  --     (Hm : ∀{a b : obC} {f : mor a b}, m f = m' f)
  --       : functor.mk C D o m i c = functor.mk C D o m' i' c' :=
  -- sorry

  -- theorem congr_functor_refl {obC obD : Type} {C : category obC} {D : category obD} {o : obC → obD}
  --     {m : Π⦃A B : obC⦄, mor A B → mor (o A) (o B)} {i i' c c'}
  --       : functor.mk C D o m i c = functor.mk C D o m i' c' :=
  -- rfl

  theorem assoc {obA obB obC obD : Type} {A : category obA} {B : category obB}
      {C : category obC} {D : category obD} (H : C ⇒ D) (G : B ⇒ C) (F : A ⇒ B) :
      H ∘∘ (G ∘∘ F) = (H ∘∘ G) ∘∘ F :=
  rfl

  -- later check whether we want implicit or explicit arguments here. For the moment, define both
  definition id {ob : Type} {C : category ob} : functor C C :=
  mk C C (λa, a) (λ a b f, f) (λ a, rfl) (λ a b c f g, rfl)
  definition ID {ob : Type} (C : category ob) : functor C C := id
  definition Id {C : Category} : Functor C C := Functor.mk id
  definition iD (C : Category) : Functor C C := Functor.mk id

  theorem id_left {obC obB : Type} {B : category obB} {C : category obC} (F : B ⇒ C)
      : id ∘∘ F = F :=
  rec (λ obF morF idF compF, rfl) F

  theorem id_right {obC obB : Type} {B : category obB} {C : category obC} (F : B ⇒ C)
      : F ∘∘ id = F :=
  rec (λ obF morF idF compF, rfl) F

  end category_functor

  section Functor
--  parameters {C D E : Category} (G : Functor D E) (F : Functor C D)
  definition Functor_functor {C D : Category} (F : Functor C D) : functor (category_instance C) (category_instance D) :=
  Functor.rec (λ x, x) F

  definition Compose {C D E : Category} (G : Functor D E) (F : Functor C D) : Functor C E :=
  Functor.mk (compose (Functor_functor G) (Functor_functor F))

--  namespace Functor
  precedence `∘∘` : 60
  infixr `∘∘` := Compose
--  end Functor

  definition Assoc {A B C D : Category} (H : Functor C D) (G : Functor B C) (F : Functor A B)
    :  H ∘∘ (G ∘∘ F) = (H ∘∘ G) ∘∘ F :=
  rfl

  theorem Id_left {B : Category} {C : Category} (F : Functor B C)
      : Id ∘∘ F = F :=
  Functor.rec (λ f, subst (id_left f) rfl) F

  theorem Id_right {B : Category} {C : Category} (F : Functor B C)
      : F ∘∘ Id = F :=
  Functor.rec (λ f, subst (id_right f) rfl) F

  end Functor

end functor

open functor

inductive natural_transformation {obC obD : Type} {C : category obC} {D : category obD}
    (F G : functor C D) : Type :=
mk : Π (η : Π(a : obC), mor (object F a) (object G a)), Π{a b : obC} (f : mor a b), morphism G f ∘ η a = η b ∘ morphism F f
 → natural_transformation F G

inductive Natural_transformation {C D : Category} (F G : Functor C D) : Type :=
mk : natural_transformation (Functor_functor F) (Functor_functor G) → Natural_transformation F G

namespace natural_tranformation

  -- todo

end natural_tranformation

open functor
namespace category
  section cat_Cat

  definition Cat : category Category :=
  mk (λ a b, Functor a b) (λ a b c g f, Compose g f) (λ a, Id)
     (λ a b c d h g f, Assoc h g f) (λ a b f, Id_left f) (λ a b f, Id_right f)

  end cat_Cat

  section slice
  open sigma

  definition slice {ob : Type} (C : category ob) (c : ob) : category (Σ(b : ob), mor b c) :=
  mk (λa b, Σ(g : mor (dpr1 a) (dpr1 b)), dpr2 b ∘ g = dpr2 a)
     (λ a b c g f, dpair (dpr1 g ∘ dpr1 f)
       (calc
         dpr2 c ∘ (dpr1 g ∘ dpr1 f) = (dpr2 c ∘ dpr1 g) ∘ dpr1 f : assoc
           ... = dpr2 b ∘ dpr1 f : {dpr2 g}
           ... = dpr2 a : {dpr2 f}))
     (λ a, dpair id id_right)
     (λ a b c d h g f, dpair_eq    assoc    proof_irrel)
     (λ a b f,         sigma.equal id_left  proof_irrel)
     (λ a b f,         sigma.equal id_right proof_irrel)
  --replacing proof_irrel with rfl confuses the unifier
  end slice


  section coslice
  open sigma

  definition coslice {ob : Type} (C : category ob) (c : ob) : category (Σ(b : ob), mor c b) :=
  mk (λa b, Σ(g : mor (dpr1 a) (dpr1 b)), g ∘ dpr2 a = dpr2 b)
     (λ a b c g f, dpair (dpr1 g ∘ dpr1 f)
       (calc
         (dpr1 g ∘ dpr1 f) ∘ dpr2 a = dpr1 g ∘ (dpr1 f ∘ dpr2 a): symm assoc
           ... = dpr1 g ∘ dpr2 b : {dpr2 f}
           ... = dpr2 c : {dpr2 g}))
     (λ a, dpair id id_left)
     (λ a b c d h g f, dpair_eq    assoc    proof_irrel)
     (λ a b f,         sigma.equal id_left  proof_irrel)
     (λ a b f,         sigma.equal id_right proof_irrel)

  -- theorem slice_coslice_opp {ob : Type} (C : category ob) (c : ob) :
  --     coslice C c = opposite (slice (opposite C) c) :=
  -- sorry
  end coslice

  section product
  open prod
  definition product {obC obD : Type} (C : category obC) (D : category obD)
      : category (obC × obD) :=
  mk (λa b, mor (pr1 a) (pr1 b) × mor (pr2 a) (pr2 b))
     (λ a b c g f, (pr1 g ∘ pr1 f , pr2 g ∘ pr2 f) )
     (λ a, (id,id))
     (λ a b c d h g f, pair_eq    assoc    assoc   )
     (λ a b f,         prod.equal id_left  id_left )
     (λ a b f,         prod.equal id_right id_right)

  end product

  section arrow
  open sigma eq_ops

  definition arrow {ob : Type} (C : category ob) : category (Σ(a b : ob), mor a b) :=
  mk (λa b, Σ(g : mor (dpr1 a) (dpr1 b)) (h : mor (dpr2' a) (dpr2' b)),
       dpr3 b ∘ g = h ∘ dpr3 a)
     (λ a b c g f, dpair (dpr1 g ∘ dpr1 f) (dpair (dpr2' g ∘ dpr2' f)
       (calc
         dpr3 c ∘ (dpr1 g ∘ dpr1 f) = (dpr3 c ∘ dpr1 g) ∘ dpr1 f : assoc
           ... = (dpr2' g ∘ dpr3 b) ∘ dpr1 f : {dpr3 g}
           ... = dpr2' g ∘ (dpr3 b ∘ dpr1 f) : symm assoc
           ... = dpr2' g ∘ (dpr2' f ∘ dpr3 a) : {dpr3 f}
           ... = (dpr2' g ∘ dpr2' f) ∘ dpr3 a : assoc)))
     (λ a, dpair id (dpair id (id_right ⬝ (symm id_left))))
     (λ a b c d h g f, dtrip_eq2   assoc    assoc    proof_irrel)
     (λ a b f,         trip.equal2 id_left  id_left  proof_irrel)
     (λ a b f,         trip.equal2 id_right id_right proof_irrel)
     -- (λ a b c d h g f, dpair_eq assoc sorry)
     -- (λ a b f,         sigma.equal id_left sorry)
     -- (λ a b f,         sigma.equal id_right sorry)
  end arrow


  -- definition foo {obC obD : Type} (C : category obC) (D : category obD)
  --     : category (obC × obD) :=
  -- mk (λa b, sorry)
  --    (λ a b c g f, sorry)
  --    (λ a, sorry)
  --    (λ a b c d h g f, sorry)
  --    (λ a b f, sorry)
  --    (λ a b f, sorry)

end category
