/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.category.basic
Author: Floris van Doorn
-/
open eq eq.ops

structure category [class] (ob : Type) : Type :=
  (hom : ob → ob → Type)
  (comp : Π⦃a b c : ob⦄, hom b c → hom a b → hom a c)
  (ID : Π (a : ob), hom a a)
  (assoc : Π ⦃a b c d : ob⦄ (h : hom c d) (g : hom b c) (f : hom a b),
     comp h (comp g f) = comp (comp h g) f)
  (id_left : Π ⦃a b : ob⦄ (f : hom a b), comp !ID f = f)
  (id_right : Π ⦃a b : ob⦄ (f : hom a b), comp f !ID = f)

attribute category [multiple-instances]

namespace category
  variables {ob : Type} [C : category ob]
  variables {a b c d : ob}
  include C

  definition compose := comp

  definition id [reducible] {a : ob} : hom a a := ID a

  infixr `∘` := comp
  infixl `⟶`:25 := hom -- input ⟶ using \--> (this is a different arrow than \-> (→))

  variables {h : hom c d} {g : hom b c} {f : hom a b} {i : hom a a}

  --the following is the only theorem for which "include C" is necessary if C is a variable (why?)
  theorem id_compose (a : ob) : (ID a) ∘ id = id := !id_left

  theorem left_id_unique (H : Π{b} {f : hom b a}, i ∘ f = f) : i = id :=
  calc i = i ∘ id : id_right
     ... = id     : H

  theorem right_id_unique (H : Π{b} {f : hom a b}, f ∘ i = f) : i = id :=
  calc i = id ∘ i : id_left
     ... = id     : H
end category

inductive Category : Type := mk : Π (ob : Type), category ob → Category

namespace category
  definition Mk {ob} (C) : Category := Category.mk ob C
  definition MK (a b c d e f g) : Category := Category.mk a (category.mk b c d e f g)

  definition objects [coercion] [reducible] (C : Category) : Type
  := Category.rec (fun c s, c) C

  definition category_instance [instance] [coercion] [reducible] (C : Category) : category (objects C)
  := Category.rec (fun c s, s) C

end category

open category

theorem Category.equal (C : Category) : Category.mk C C = C :=
Category.rec (λ ob c, rfl) C
