/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad
-/
prelude
import init.datatypes init.logic
open decidable

universe variables u

structure subtype {A : Type u} (p : A → Prop) :=
tag :: (elt_of : A) (has_property : p elt_of)

namespace subtype

  def exists_of_subtype {A : Type u} {p : A → Prop} : { x // p x } → ∃ x, p x
  | ⟨a, h⟩ := ⟨a, h⟩

  variables {A : Type u} {p : A → Prop}

  lemma tag_irrelevant {a : A} (h1 h2 : p a) : tag a h1 = tag a h2 :=
  rfl

  protected lemma eq : ∀ {a1 a2 : {x // p x}}, elt_of a1 = elt_of a2 → a1 = a2
  | ⟨x, h1⟩ ⟨.x, h2⟩ rfl := rfl

end subtype

open subtype

instance {A : Type u} {p : A → Prop} {a : A} (h : p a) : inhabited {x // p x} :=
⟨⟨a, h⟩⟩
