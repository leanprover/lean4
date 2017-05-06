/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad
-/
prelude
import init.logic
open decidable

universes u

namespace subtype

def exists_of_subtype {α : Type u} {p : α → Prop} : { x // p x } → ∃ x, p x
| ⟨a, h⟩ := ⟨a, h⟩

variables {α : Type u} {p : α → Prop}

lemma tag_irrelevant {a : α} (h1 h2 : p a) : mk a h1 = mk a h2 :=
rfl

protected lemma eq : ∀ {a1 a2 : {x // p x}}, val a1 = val a2 → a1 = a2
| ⟨x, h1⟩ ⟨.(x), h2⟩ rfl := rfl

@[simp] lemma eta (a : {x // p x}) (h : p (val a)) : mk (val a) h = a :=
subtype.eq rfl

end subtype

open subtype

instance {α : Type u} {p : α → Prop} {a : α} (h : p a) : inhabited {x // p x} :=
⟨⟨a, h⟩⟩
