/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad
-/
prelude
import init.datatypes init.logic
open decidable

universe variables u

structure subtype {A : Type u} (P : A → Prop) :=
tag :: (elt_of : A) (has_property : P elt_of)

notation `{` binder ` \ `:0 r:(scoped:1 P, subtype P) `}` := r

namespace subtype

  definition exists_of_subtype {A : Type u} {P : A → Prop} : { x \ P x } → ∃ x, P x
  | ⟨a, h⟩ := ⟨a, h⟩

  variables {A : Type u} {P : A → Prop}

  theorem tag_irrelevant {a : A} (h1 h2 : P a) : tag a h1 = tag a h2 :=
  rfl

  protected theorem eq : ∀ {a1 a2 : {x \ P x}}, elt_of a1 = elt_of a2 → a1 = a2
  | ⟨x, h1⟩ ⟨.x, h2⟩ rfl := rfl

end subtype

open subtype

variables {A : Type u} {P : A → Prop}

attribute [instance]
protected definition subtype.is_inhabited {a : A} (h : P a) : inhabited {x \ P x} :=
⟨⟨a, h⟩⟩
