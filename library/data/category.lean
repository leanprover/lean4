-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Floris van Doorn

-- category
import logic.core.eq logic.core.connectives
import data.unit data.sigma data.prod
import struc.function

inductive category (ob : Type) (mor : ob → ob → Type) : Type :=
mk : Π (comp : Π⦃A B C : ob⦄, mor B C → mor A B → mor A C)
           (id : Π {A : ob}, mor A A),
            (Π {A B C D : ob} {f : mor A B} {g : mor B C} {h : mor C D},
            comp h (comp g f) = comp (comp h g) f) →
           (Π {A B : ob} {f : mor A B}, comp f id = f) →
           (Π {A B : ob} {f : mor A B}, comp id f = f) →
            category ob mor
class category

namespace category
  precedence `∘` : 60

  section
  parameters {ob : Type} {mor : ob → ob → Type} {Cat : category ob mor}
  abbreviation compose := rec (λ comp id assoc idr idl, comp) Cat
  abbreviation id := rec (λ comp id assoc idr idl, id) Cat
  abbreviation ID (A : ob) := @id A
  end

  infixr `∘` := compose

  section
  parameters {ob : Type} {mor : ob → ob → Type} {Cat : category ob mor}

  theorem assoc : Π {A B C D : ob} {f : mor A B} {g : mor B C} {h : mor C D},
                h ∘ (g ∘ f) = (h ∘ g) ∘ f :=
  rec (λ comp id assoc idr idl, assoc) Cat

  theorem id_right : Π {A B : ob} {f : mor A B}, f ∘ id = f :=
  rec (λ comp id assoc idr idl, idr) Cat
  theorem id_left  : Π {A B : ob} {f : mor A B}, id ∘ f = f :=
  rec (λ comp id assoc idr idl, idl) Cat

  theorem left_id_unique {A : ob} (i : mor A A) (H : Π{B} {f : mor B A}, i ∘ f = f) : i = id :=
  calc
    i = i ∘ id : eq.symm id_right
    ... = id : H

  theorem right_id_unique {A : ob} (i : mor A A) (H : Π{B} {f : mor A B}, f ∘ i = f) : i = id :=
  calc
    i = id ∘ i : eq.symm id_left
    ... = id : H

  definition has_left_inverse {A B : ob} (f : mor A B) : Type :=
  including Cat, Σ g, g ∘ f = id

  definition left_inverse {A B : ob} (f : mor A B) (H : has_left_inverse f) : mor B A :=
  sigma.dpr1 H

  definition has_right_inverse {A B : ob} (f : mor A B) : Type :=
  including Cat, Σ g, f ∘ g = id

  definition right_inverse {A B : ob} (f : mor A B) (H : has_right_inverse f) : mor B A :=
  sigma.dpr1 H

  definition iso {A B : ob} (f : mor A B) : Type :=
  including Cat, Σ g, f ∘ g = id ∧ g ∘ f = id

  definition inverse {A B : ob} (f : mor A B) (H : iso f) : mor B A :=
  sigma.dpr1 H

  theorem iso_imp_left_inverse {A B : ob} (f : mor A B) (H : iso f) : has_left_inverse f :=
  sorry

  theorem iso_imp_right_inverse {A B : ob} (f : mor A B) (H : iso f) : has_left_inverse f :=
  sorry

  theorem left_right_inverse_imp_iso {A B : ob} (f : mor A B)
    (Hl : has_left_inverse f) (Hr : has_right_inverse f) : iso f :=
  sorry

  postfix `⁻¹` := inverse

  set_option pp.implicit true

  -- theorem foo {A B : ob} {f : mor A B} (H : iso f) : true :=
  -- including Cat, (λx (y : iso f),x) _ H

  theorem compose_inverse {A B : ob} {f : mor A B} (H : iso f) : f ∘ f⁻¹ H = id :=
  and.elim_left (sigma.dpr2 H)

  theorem inverse_compose {A B : ob} {f : mor A B} (H : iso f) : f⁻¹ H ∘ f = id :=
  and.elim_right (sigma.dpr2 H)

  theorem inverse_unique {A B : ob} {f : mor A B} (H H' : iso f) : f⁻¹ H = f⁻¹ H' :=
  sorry
  -- calc
  --  inverse f H = f⁻¹ H ∘ id : symm id.right
  --    ... = f⁻¹ H ∘ f ∘ f⁻¹ H' : {symm (compose_inverse H')}
  --    ... = (f⁻¹ H ∘ f) ∘ f⁻¹ H' : assoc
  --    ... = id ∘ f⁻¹ H' : {inverse_compose H}
  --    ... = f⁻¹ H' : id.left

  definition mono {A B : ob} (f : mor A B) : Prop :=
  including Cat, ∀⦃C⦄ {g h : mor C A}, f ∘ g = f ∘ h → g = h

  definition epi  {A B : ob} (f : mor A B) : Prop :=
  including Cat, ∀⦃C⦄ {g h : mor B C}, g ∘ f = h ∘ f → g = h
  end

  postfix `⁻¹` := inverse

  section
  parameters {obC obD : Type} {morC : obC → obC → Type} {morD : obD → obD → Type}
  parameters (C : category obC morC)
  parameters (D : category obD morD)

  definition tst (a b c : obC) (m1 : morC a b) (m2 : morC b c) :=
  (λx y, x) (compose m2 m1) (including C, false)

  definition tst2 (C : category obC morC) (a b c : obC) (m1 : morC a b) (m2 : morC b c) :=
  compose m2 m1

  parameter a : obC
  parameter f : morC a a

  -- inductive foo : Type :=
  -- mk : including C, foo

  -- inductive functor : Type :=
  -- functor.mk : including C D,
  --             Π (obF : obC → obD) (morF : Π{A B}, morC A B → morD (obF A) (obF B)),
  --            (Π {A : obC}, morF (ID A) = ID (obF A)) →
  --            (Π {A B C : obC} {f : morC A B} {g : morC B C}, morF (g ∘ f) = morF g ∘ morF f) →
  --             functor
  end

  section
  open unit
  definition one [instance] : category unit (λa b, unit) :=
  category.mk (λ a b c f g, star) (λ a, star) (λ a b c d f g h, unit.equal _ _)
    (λ a b f, unit.equal _ _) (λ a b f, unit.equal _ _)
  end

  section
  --need extensionality
  definition type_cat : category Type (λA B, A → B) :=
  mk (λ a b c f g, function.compose f g) (λ a, function.id) (λ a b c d f g h, sorry)
    (λ a b f, sorry) (λ a b f, sorry)
  end
end category
