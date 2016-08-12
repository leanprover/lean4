/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad
-/
prelude
import init.datatypes init.logic
open decidable

structure subtype {A : Type} (P : A → Prop) :=
tag :: (elt_of : A) (has_property : P elt_of)

notation `{` binder ` \ `:0 r:(scoped:1 P, subtype P) `}` := r

namespace subtype

  definition exists_of_subtype {A : Type} {P : A → Prop} : { x \ P x } → ∃ x, P x
  | (subtype.tag a h) := exists.intro a h

  variables {A : Type} {P : A → Prop}

  theorem tag_irrelevant {a : A} (H1 H2 : P a) : tag a H1 = tag a H2 :=
  rfl

  theorem tag_eq {a1 a2 : A} {H1 : P a1} {H2 : P a2} (H3 : a1 = a2) : tag a1 H1 = tag a2 H2 :=
  eq.subst H3 (tag_irrelevant H1) H2

  protected theorem eq : ∀ {a1 a2 : {x \ P x}} (H : elt_of a1 = elt_of a2), a1 = a2
  | (tag x1 H1) (tag x2 H2) := tag_eq
end subtype

open subtype

variables {A : Type} {P : A → Prop}
attribute [instance]
protected definition subtype.is_inhabited {a : A} (H : P a) : inhabited {x \ P x} :=
inhabited.mk (tag a H)
