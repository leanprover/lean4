/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

prelude
public import Init.Ext

public section

namespace Subtype

universe u
variable {α : Sort u} {p q : α → Prop}

@[simp]
protected theorem «forall» {q : { a // p a } → Prop} : (∀ x, q x) ↔ ∀ a b, q ⟨a, b⟩ :=
  ⟨fun h a b ↦ h ⟨a, b⟩, fun h ⟨a, b⟩ ↦ h a b⟩

@[simp]
protected theorem «exists» {q : { a // p a } → Prop} :
    (Exists fun x => q x) ↔ Exists fun a => Exists fun b => q ⟨a, b⟩ :=
  ⟨fun ⟨⟨a, b⟩, h⟩ ↦ ⟨a, b, h⟩, fun ⟨a, b, h⟩ ↦ ⟨⟨a, b⟩, h⟩⟩

end Subtype
