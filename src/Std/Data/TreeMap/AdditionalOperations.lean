/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.TreeMap.Basic
import Std.Data.TreeMap.Raw
import Std.Data.DTreeMap.AdditionalOperations

/-!
# Additional dependent tree map operations

This file defines more operations on `Std.TreeMap`.
We currently do not provide lemmas for these functions.
-/

set_option autoImplicit false
set_option linter.missingDocs true

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w} {cmp : α → α → Ordering}

namespace Std.TreeMap

namespace Raw

@[inline, inherit_doc DTreeMap.Raw.filterMap]
def filterMap (f : (a : α) → β → Option γ) (t : Raw α β cmp) : Raw α γ cmp :=
  ⟨t.inner.filterMap f⟩

@[inline, inherit_doc DTreeMap.Raw.map]
def map (f : α → β → γ) (t : Raw α β cmp) : Raw α γ cmp :=
  ⟨t.inner.map f⟩

end Raw

@[inline, inherit_doc DTreeMap.filterMap]
def filterMap (f : (a : α) → β → Option γ) (m : TreeMap α β cmp) : TreeMap α γ cmp :=
  ⟨m.inner.filterMap f⟩

@[inline, inherit_doc DTreeMap.map]
def map (f : α → β → γ) (t : TreeMap α β cmp) : TreeMap α γ cmp :=
  ⟨t.inner.map f⟩

end Std.TreeMap
