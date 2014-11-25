-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Floris van Doorn

import logic.axioms.funext

open eq eq.ops

structure category [class] (ob : Type) : Type :=
  (hom : ob → ob → Type)
  (compose : Π⦃a b c : ob⦄, hom b c → hom a b → hom a c)
  (ID : Π (a : ob), hom a a)
  (assoc : Π ⦃a b c d : ob⦄ (h : hom c d) (g : hom b c) (f : hom a b),
     compose h (compose g f) = compose (compose h g) f)
  (id_left : Π ⦃a b : ob⦄ (f : hom a b), compose !ID f = f)
  (id_right : Π ⦃a b : ob⦄ (f : hom a b), compose f !ID = f)

namespace category
  variables {ob : Type} [C : category ob]
  variables {a b c d : ob} {h : hom c d} {g : hom b c} {f : hom a b} {i : hom a a}
  include C

  definition id [reducible] {a : ob} : hom a a := ID a

  infixr `∘` := compose
  infixl `⟶`:25 := hom -- input ⟶ using \--> (this is a different arrow than \-> (→))

  theorem id_compose (a : ob) : (ID a) ∘ id = id := !id_left

  theorem left_id_unique (H : Π{b} {f : hom b a}, i ∘ f = f) : i = id :=
  calc i = i ∘ id : id_right
     ... = id     : H

  theorem right_id_unique (H : Π{b} {f : hom a b}, f ∘ i = f) : i = id :=
  calc i = id ∘ i : id_left
     ... = id     : H
end category

structure Category : Type :=
  (objects : Type)
  (category_instance : category objects)

namespace category
  definition Mk {ob} (C) : Category := Category.mk ob C
  definition MK (o h c i a l r) : Category := Category.mk o (category.mk h c i a l r)
  definition objects [coercion] [reducible] := Category.objects
  definition category_instance [instance] [coercion] [reducible] := Category.category_instance
end category

open category

theorem Category.equal (C : Category) : Category.mk C C = C :=
Category.rec (λ ob c, rfl) C
