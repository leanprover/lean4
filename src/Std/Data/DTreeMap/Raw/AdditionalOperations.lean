/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Std.Data.DTreeMap.AdditionalOperations

@[expose] public section

/-!
# Additional dependent raw tree map operations

This file defines more operations on `Std.DTreeMap.Raw`.
We currently do not provide lemmas for these functions.
-/

set_option autoImplicit false
set_option linter.missingDocs true

universe u v w

variable {α : Type u} {β : α → Type v} {γ : α → Type w} {cmp : α → α → Ordering}

namespace Std.DTreeMap
open Internal (Impl)

namespace Raw
local instance : Coe (Type v) (α → Type v) where coe γ := fun _ => γ

@[inline, inherit_doc DTreeMap.filterMap]
def filterMap (f : (a : α) → β a → Option (γ a)) (t : Raw α β cmp) : Raw α γ cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.filterMap! f⟩

@[inline, inherit_doc DTreeMap.map]
def map (f : (a : α) → β a → γ a) (t : Raw α β cmp) : Raw α γ cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.map f⟩

/-!
We do not provide `get*GE`, `get*GT`, `get*LE` and `get*LT` functions for the raw trees.
-/

end Raw

end Std.DTreeMap
