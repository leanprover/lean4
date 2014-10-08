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
  section
  variables {obC obD : Type} {C : category obC} {D : category obD} {F₁ F₂ F₃ F₄ : C ⇒ D}
  protected theorem assoc (η₃ : F₃ ==> F₄) (η₂ : F₂ ==> F₃) (η₁ : F₁ ==> F₂) :
      η₃ ∘n (η₂ ∘n η₁) = (η₃ ∘n η₂) ∘n η₁ :=
  congr_arg2_dep mk (funext (take x, !assoc)) proof_irrel

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

  protected theorem id_left (η : F₁ ==> F₂) : natural_transformation.compose id η = η :=
  rec (λf H, congr_arg2_dep mk (funext (take x, !id_left)) proof_irrel) η

  protected theorem id_right (η : F₁ ==> F₂) : natural_transformation.compose η id = η :=
  rec (λf H, congr_arg2_dep mk (funext (take x, !id_right)) proof_irrel) η

  end
end natural_transformation

-- examples of categories / basic constructions (TODO: move to separate file)

open functor
namespace category
  section
  open unit
  definition one [instance] : category unit :=
  category.mk (λa b, unit) (λ a b c f g, star) (λ a, star) (λ a b c d f g h, unit.equal _ _)
    (λ a b f, unit.equal _ _) (λ a b f, unit.equal _ _)
  end

  section
  open unit
  definition big_one_test (A : Type) : category A :=
  category.mk (λa b, unit) (λ a b c f g, star) (λ a, star) (λ a b c d f g h, unit.equal _ _)
    (λ a b f, unit.equal _ _) (λ a b f, unit.equal _ _)
  end

  section
  parameter {ob : Type}
  definition opposite (C : category ob) : category ob :=
  category.mk (λa b, hom b a) (λ a b c f g, g ∘ f) (λ a, id) (λ a b c d f g h, symm !assoc)
    (λ a b f, !id_right) (λ a b f, !id_left)
  precedence `∘op` : 60
  infixr `∘op` := @compose _ (opposite _) _ _ _

  parameters {C : category ob} {a b c : ob}

  theorem compose_op {f : @hom ob C a b} {g : hom b c} : f ∘op g = g ∘ f :=
  rfl

  theorem op_op {C : category ob} : opposite (opposite C) = C :=
  category.rec (λ hom comp id assoc idl idr, refl (mk _ _ _ _ _ _)) C
  end

  definition Opposite (C : Category) : Category :=
  Category.mk (objects C) (opposite (category_instance C))


  section
  definition type_category : category Type :=
  mk (λA B, A → B) (λ a b c, function.compose) (λ a, function.id)
    (λ a b c d h g f, symm (function.compose_assoc h g f))
    (λ a b f, function.compose_id_left f) (λ a b f, function.compose_id_right f)
  end

  section cat_C

  definition C : category Category :=
  mk (λ a b, Functor a b) (λ a b c g f, functor.Compose g f) (λ a, functor.Id)
     (λ a b c d h g f, !functor.Assoc) (λ a b f, !functor.Id_left)
     (λ a b f, !functor.Id_right)

  end cat_C

  section functor_category
  parameters {obC obD : Type} (C : category obC) (D : category obD)
  definition functor_category : category (functor C D) :=
  mk (λa b, natural_transformation a b)
     (λ a b c g f, natural_transformation.compose g f)
     (λ a, natural_transformation.id)
     (λ a b c d h g f, !natural_transformation.assoc)
     (λ a b f, !natural_transformation.id_left)
     (λ a b f, !natural_transformation.id_right)
  end functor_category


  section slice
  open sigma

  definition slice {ob : Type} (C : category ob) (c : ob) : category (Σ(b : ob), hom b c) :=
  mk (λa b, Σ(g : hom (dpr1 a) (dpr1 b)), dpr2 b ∘ g = dpr2 a)
     (λ a b c g f, dpair (dpr1 g ∘ dpr1 f)
       (show dpr2 c ∘ (dpr1 g ∘ dpr1 f) = dpr2 a,
         proof
         calc
           dpr2 c ∘ (dpr1 g ∘ dpr1 f) = (dpr2 c ∘ dpr1 g) ∘ dpr1 f : !assoc
             ... = dpr2 b ∘ dpr1 f : {dpr2 g}
             ... = dpr2 a : {dpr2 f}
         qed))
     (λ a, dpair id !id_right)
     (λ a b c d h g f, dpair_eq    !assoc    proof_irrel)
     (λ a b f,         sigma.equal !id_left  proof_irrel)
     (λ a b f,         sigma.equal !id_right proof_irrel)
  -- We give proof_irrel instead of rfl, to give the unifier an easier time
  end slice

  section coslice
  open sigma

  definition coslice {ob : Type} (C : category ob) (c : ob) : category (Σ(b : ob), hom c b) :=
  mk (λa b, Σ(g : hom (dpr1 a) (dpr1 b)), g ∘ dpr2 a = dpr2 b)
     (λ a b c g f, dpair (dpr1 g ∘ dpr1 f)
       (show (dpr1 g ∘ dpr1 f) ∘ dpr2 a = dpr2 c,
         proof
         calc
           (dpr1 g ∘ dpr1 f) ∘ dpr2 a = dpr1 g ∘ (dpr1 f ∘ dpr2 a): symm !assoc
             ... = dpr1 g ∘ dpr2 b : {dpr2 f}
             ... = dpr2 c : {dpr2 g}
         qed))
     (λ a, dpair id !id_left)
     (λ a b c d h g f, dpair_eq    !assoc    proof_irrel)
     (λ a b f,         sigma.equal !id_left  proof_irrel)
     (λ a b f,         sigma.equal !id_right proof_irrel)

  -- theorem slice_coslice_opp {ob : Type} (C : category ob) (c : ob) :
  --     coslice C c = opposite (slice (opposite C) c) :=
  -- sorry
  end coslice

  section product
  open prod
  definition product {obC obD : Type} (C : category obC) (D : category obD)
      : category (obC × obD) :=
  mk (λa b, hom (pr1 a) (pr1 b) × hom (pr2 a) (pr2 b))
     (λ a b c g f, (pr1 g ∘ pr1 f , pr2 g ∘ pr2 f) )
     (λ a, (id,id))
     (λ a b c d h g f, pair_eq    !assoc    !assoc   )
     (λ a b f,         prod.equal !id_left  !id_left )
     (λ a b f,         prod.equal !id_right !id_right)

  end product

  section arrow
  open sigma eq.ops
  -- theorem concat_commutative_squares {ob : Type} {C : category ob} {a1 a2 a3 b1 b2 b3 : ob}
  --     {f1 : a1 => b1} {f2 : a2 => b2} {f3 : a3 => b3} {g2 : a2 => a3} {g1 : a1 => a2}
  --     {h2 : b2 => b3} {h1 : b1 => b2} (H1 : f2 ∘ g1 = h1 ∘ f1) (H2 : f3 ∘ g2 = h2 ∘ f2)
  --       : f3 ∘ (g2 ∘ g1) = (h2 ∘ h1) ∘ f1 :=
  -- calc
  --   f3 ∘ (g2 ∘ g1) = (f3 ∘ g2) ∘ g1 : assoc
  --     ... = (h2 ∘ f2) ∘ g1 : {H2}
  --     ... = h2 ∘ (f2 ∘ g1) : symm assoc
  --     ... = h2 ∘ (h1 ∘ f1) : {H1}
  --     ... = (h2 ∘ h1) ∘ f1 : assoc

  -- definition arrow {ob : Type} (C : category ob) : category (Σ(a b : ob), hom a b) :=
  -- mk (λa b, Σ(g : hom (dpr1 a) (dpr1 b)) (h : hom (dpr2' a) (dpr2' b)),
  --      dpr3 b ∘ g = h ∘ dpr3 a)
  --    (λ a b c g f, dpair (dpr1 g ∘ dpr1 f) (dpair (dpr2' g ∘ dpr2' f) (concat_commutative_squares (dpr3 f) (dpr3 g))))
  --    (λ a, dpair id (dpair id (id_right ⬝ (symm id_left))))
  --    (λ a b c d h g f, dtrip_eq2   assoc    assoc    proof_irrel)
  --    (λ a b f,         trip.equal2 id_left  id_left  proof_irrel)
  --    (λ a b f,         trip.equal2 id_right id_right proof_irrel)

  variables {ob : Type} {C : category ob}
  protected definition arrow_obs (ob : Type) (C : category ob) := Σ(a b : ob), hom a b
  variables {a b : arrow_obs ob C}
  protected definition src    (a : arrow_obs ob C) : ob                  := dpr1 a
  protected definition dst    (a : arrow_obs ob C) : ob                  := dpr2' a
  protected definition to_hom (a : arrow_obs ob C) : hom (src a) (dst a) := dpr3 a

  protected definition arrow_hom (a b : arrow_obs ob C) : Type :=
  Σ (g : hom (src a) (src b)) (h : hom (dst a) (dst b)), to_hom b ∘ g = h ∘ to_hom a

  protected definition hom_src (m : arrow_hom a b) : hom (src a) (src b) := dpr1 m
  protected definition hom_dst (m : arrow_hom a b) : hom (dst a) (dst b) := dpr2' m
  protected definition commute (m : arrow_hom a b) : to_hom b ∘ (hom_src m) = (hom_dst m) ∘ to_hom a
  := dpr3 m

  definition arrow (ob : Type) (C : category ob) : category (arrow_obs ob C) :=
  mk (λa b, arrow_hom a b)
     (λ a b c g f, dpair (hom_src g ∘ hom_src f) (dpair (hom_dst g ∘ hom_dst f)
        (show to_hom c ∘ (hom_src g ∘ hom_src f) = (hom_dst g ∘ hom_dst f) ∘ to_hom a,
         proof
         calc
         to_hom c ∘ (hom_src g ∘ hom_src f) = (to_hom c ∘ hom_src g) ∘ hom_src f : !assoc
           ... = (hom_dst g ∘ to_hom b) ∘ hom_src f  : {commute g}
           ... = hom_dst g ∘ (to_hom b ∘ hom_src f)  : symm !assoc
           ... = hom_dst g ∘ (hom_dst f ∘ to_hom a)  : {commute f}
           ... = (hom_dst g ∘ hom_dst f) ∘ to_hom a  : !assoc
         qed)
       ))
     (λ a, dpair id (dpair id (!id_right ⬝ (symm !id_left))))
     (λ a b c d h g f, dtrip_eq_ndep   !assoc    !assoc    proof_irrel)
     (λ a b f,         trip.equal_ndep !id_left  !id_left  proof_irrel)
     (λ a b f,         trip.equal_ndep !id_right !id_right proof_irrel)

  end arrow

  -- definition foo
  --     : category (sorry) :=
  -- mk (λa b, sorry)
  --    (λ a b c g f, sorry)
  --    (λ a, sorry)
  --    (λ a b c d h g f, sorry)
  --    (λ a b f, sorry)
  --    (λ a b f, sorry)

end category
