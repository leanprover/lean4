-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Floris van Doorn

open eq is_trunc

structure precategory [class] (ob : Type) : Type :=
  (hom : ob → ob → Type)
  (homH : Π {a b : ob}, is_hset (hom a b))
  (comp : Π⦃a b c : ob⦄, hom b c → hom a b → hom a c)
  (ID : Π (a : ob), hom a a)
  (assoc : Π ⦃a b c d : ob⦄ (h : hom c d) (g : hom b c) (f : hom a b),
     comp h (comp g f) = comp (comp h g) f)
  (id_left : Π ⦃a b : ob⦄ (f : hom a b), comp !ID f = f)
  (id_right : Π ⦃a b : ob⦄ (f : hom a b), comp f !ID = f)

attribute precategory [multiple-instances]

namespace precategory
  variables {ob : Type} [C : precategory ob]
  variables {a b c d : ob}
  include C
  attribute homH [instance]

  definition compose [reducible] := comp

  definition id [reducible] {a : ob} : hom a a := ID a

  infixr `∘` := comp
  infixl `⟶`:25 := hom -- input ⟶ using \--> (this is a different arrow than \-> (→))

  variables {h : hom c d} {g : hom b c} {f : hom a b} {i : hom a a}

  theorem id_compose (a : ob) : ID a ∘ ID a = ID a := !id_left

  theorem left_id_unique (H : Π{b} {f : hom b a}, i ∘ f = f) : i = id :=
  calc i = i ∘ id : id_right
     ... = id     : H

  theorem right_id_unique (H : Π{b} {f : hom a b}, f ∘ i = f) : i = id :=
  calc i = id ∘ i : id_left
     ... = id     : H

  definition homset [reducible] (x y : ob) : hset :=
  hset.mk (hom x y) _

end precategory

structure Precategory : Type :=
  (objects : Type)
  (category_instance : precategory objects)

namespace precategory
  definition Mk {ob} (C) : Precategory := Precategory.mk ob C
  definition MK (a b c d e f g h) : Precategory := Precategory.mk a (precategory.mk b c d e f g h)

  definition objects [coercion] [reducible] := Precategory.objects
  definition category_instance [instance] [coercion] [reducible] := Precategory.category_instance
  notation g `∘⁅` C `⁆` f := @compose (objects C) (category_instance C) _ _ _ g f
  -- TODO: make this left associative
  -- TODO: change this notation?

end precategory

open precategory

protected definition Precategory.eta (C : Precategory) : Precategory.mk C C = C :=
Precategory.rec (λob c, idp) C
