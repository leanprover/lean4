-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Floris van Doorn

-- category
import logic.core.eq logic.core.connectives
import data.unit data.sigma data.prod
import struc.function

inductive category [class] (ob : Type) (mor : ob → ob → Type) : Type :=
mk : Π (comp : Π⦃A B C : ob⦄, mor B C → mor A B → mor A C)
           (id : Π {A : ob}, mor A A),
            (Π {A B C D : ob} {f : mor A B} {g : mor B C} {h : mor C D},
            comp h (comp g f) = comp (comp h g) f) →
           (Π {A B : ob} {f : mor A B}, comp f id = f) →
           (Π {A B : ob} {f : mor A B}, comp id f = f) →
            category ob mor

namespace category
  precedence `∘` : 60

  section
  parameters {ob : Type} {mor : ob → ob → Type} {Cat : category ob mor}
  abbreviation compose := rec (λ comp id assoc idr idl, comp) Cat
  abbreviation id := rec (λ comp id assoc idr idl, id) Cat
  abbreviation ID (A : ob) := @id A

  infixr `∘` := compose

  theorem assoc : Π {A B C D : ob} {f : mor A B} {g : mor B C} {h : mor C D},
                h ∘ (g ∘ f) = (h ∘ g) ∘ f :=
  rec (λ comp id assoc idr idl, assoc) Cat

  theorem id_right : Π {A B : ob} {f : mor A B}, f ∘ id = f :=
  rec (λ comp id assoc idr idl, idr) Cat
  theorem id_left  : Π {A B : ob} {f : mor A B}, id ∘ f = f :=
  rec (λ comp id assoc idr idl, idl) Cat

  theorem id_left2 {A B : ob} {f : mor A B} : id ∘ f = f :=
  rec (λ comp id assoc idr idl, idl A B f) Cat
  end
end category
