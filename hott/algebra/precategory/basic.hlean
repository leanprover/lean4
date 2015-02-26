/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.precategory.basic
Authors: Floris van Doorn
-/

open eq is_trunc

namespace category

  structure precategory [class] (ob : Type) : Type :=
    (hom : ob → ob → Type)
    (homH : Π(a b : ob), is_hset (hom a b))
    (comp : Π⦃a b c : ob⦄, hom b c → hom a b → hom a c)
    (ID : Π (a : ob), hom a a)
    (assoc : Π ⦃a b c d : ob⦄ (h : hom c d) (g : hom b c) (f : hom a b),
       comp h (comp g f) = comp (comp h g) f)
    (id_left : Π ⦃a b : ob⦄ (f : hom a b), comp !ID f = f)
    (id_right : Π ⦃a b : ob⦄ (f : hom a b), comp f !ID = f)

  attribute precategory [multiple-instances]
  attribute precategory.homH [instance]

  infixr `∘` := precategory.comp
  -- input ⟶ using \--> (this is a different arrow than \-> (→))
  infixl [parsing-only] `⟶`:25 := precategory.hom
  namespace hom
    infixl `⟶` := precategory.hom -- if you open this namespace, hom a b is printed as a ⟶ b
  end hom

  abbreviation hom      := @precategory.hom
  abbreviation homH     := @precategory.homH
  abbreviation comp     := @precategory.comp
  abbreviation ID       := @precategory.ID
  abbreviation assoc    := @precategory.assoc
  abbreviation id_left  := @precategory.id_left
  abbreviation id_right := @precategory.id_right

  section basic_lemmas
  variables {ob : Type} [C : precategory ob]
  variables {a b c d : ob} {h : c ⟶ d} {g : hom b c} {f f' : hom a b} {i : a ⟶ a}
  include C

  definition id [reducible] := ID a

  definition id_compose (a : ob) : ID a ∘ ID a = ID a := !id_left

  definition left_id_unique (H : Π{b} {f : hom b a}, i ∘ f = f) : i = id :=
  calc i = i ∘ id : id_right
     ... = id     : H

  definition right_id_unique (H : Π{b} {f : hom a b}, f ∘ i = f) : i = id :=
  calc i = id ∘ i : id_left
     ... = id     : H

  definition homset [reducible] (x y : ob) : hset :=
  hset.mk (hom x y) _

  definition is_hprop_eq_hom [instance] : is_hprop (f = f') :=
  !is_trunc_eq
  end basic_lemmas

  structure Precategory : Type :=
    (carrier : Type)
    (struct : precategory carrier)

  definition precategory.Mk [reducible] {ob} (C) : Precategory := Precategory.mk ob C
  definition precategory.MK [reducible] (a b c d e f g h) : Precategory :=
  Precategory.mk a (precategory.mk b c d e f g h)

  abbreviation carrier := @Precategory.carrier

  attribute Precategory.carrier [coercion]
  attribute Precategory.struct [instance] [priority 10000] [coercion]
  -- definition precategory.carrier [coercion] [reducible] := Precategory.carrier
  -- definition precategory.struct [instance] [coercion] [reducible] := Precategory.struct
  notation g `∘⁅` C `⁆` f := @comp (Precategory.carrier C) (Precategory.struct C) _ _ _ g f
  -- TODO: make this left associative
  -- TODO: change this notation?

  definition Precategory.eta (C : Precategory) : Precategory.mk C C = C :=
  Precategory.rec (λob c, idp) C

end category

open category
