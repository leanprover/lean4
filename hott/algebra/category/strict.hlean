/-
Copyright (c) 2015 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jakob von Raumer
-/

import .precategory .functor

open is_trunc eq

namespace category
  structure strict_precategory [class] (ob : Type) extends precategory ob :=
  mk' :: (is_hset_ob : is_hset ob)

  attribute strict_precategory.is_hset_ob [instance]

  definition strict_precategory.mk [reducible] {ob : Type} (C : precategory ob)
    (H : is_hset ob) : strict_precategory ob :=
  precategory.rec_on C strict_precategory.mk' H

  structure Strict_precategory : Type :=
    (carrier : Type)
    (struct : strict_precategory carrier)

  attribute Strict_precategory.struct [instance] [coercion]

  definition Strict_precategory.to_Precategory [coercion] [reducible]
    (C : Strict_precategory) : Precategory :=
  Precategory.mk (Strict_precategory.carrier C) C

  open functor

  -- TODO: move to constructions.cat?
  definition precategory_strict_precategory [constructor] : precategory Strict_precategory :=
  precategory.mk (λ A B, A ⇒ B)
                 (λ A B C G F, G ∘f F)
                 (λ A, 1)
                 (λ A B C D, functor.assoc)
                 (λ A B, functor.id_left)
                 (λ A B, functor.id_right)

  definition Precategory_strict_precategory [constructor] := precategory.Mk precategory_strict_precategory

  namespace ops
    abbreviation Cat := Precategory_strict_precategory
  end ops

end category

  /-section
  open decidable unit empty
  variables {A : Type} [H : decidable_eq A]
  include H
  definition set_hom (a b : A) := decidable.rec_on (H a b) (λh, unit) (λh, empty)
  theorem set_hom_subsingleton [instance] (a b : A) : subsingleton (set_hom a b) := _
  definition set_compose {a b c : A} (g : set_hom b c) (f : set_hom a b) : set_hom a c :=
  decidable.rec_on
    (H b c)
    (λ Hbc g, decidable.rec_on
      (H a b)
      (λ Hab f, rec_on_true (trans Hab Hbc) ⋆)
      (λh f, empty.rec _ f) f)
    (λh (g : empty), empty.rec _ g) g
  omit H
  definition discrete_precategory (A : Type) [H : decidable_eq A] : precategory A :=
  mk (λa b, set_hom a b)
     (λ a b c g f, set_compose g f)
     (λ a, decidable.rec_on_true rfl ⋆)
     (λ a b c d h g f, @subsingleton.elim (set_hom a d) _ _ _)
     (λ a b f, @subsingleton.elim (set_hom a b) _ _ _)
     (λ a b f, @subsingleton.elim (set_hom a b) _ _ _)
  definition Discrete_category (A : Type) [H : decidable_eq A] := Mk (discrete_category A)
  end
  section
  open unit bool
  definition category_one := discrete_category unit
  definition Category_one := Mk category_one
  definition category_two := discrete_category bool
  definition Category_two := Mk category_two
  end-/
