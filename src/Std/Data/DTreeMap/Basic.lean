/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Orderedtree.DTreeMap.Internal.Impl

set_option autoImplicit false
set_option linter.missingDocs true

universe u v

variable {α : Type u} {β : α → Type v} {cmp : α → α → Ordering}

namespace Std

/-- Binary search trees. -/
structure DTreeMap (α : Type u) (β : α → Type v) (cmp : α → α → Ordering) where
  /-- Internal implementation detail of the tree map. -/
  inner : DTreeMap.Internal.Impl α β
  /-- Internal implementation detail of the tree map. -/
  wf : letI : Ord α := ⟨cmp⟩; inner.WF

namespace DTreeMap

@[inline]
def isEmpty (t : DTreeMap α β cmp) : Bool :=
  t.inner.isEmpty

/-- Creates a new empty tree map. -/
@[inline]
def empty : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨Internal.Impl.empty, .empty⟩

/-- Inserts the mapping `(a, b)` into the tree map. -/
@[inline]
def insert (l : DTreeMap α β cmp) (a : α) (b : β a) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨(l.inner.insert a b l.wf.balanced).impl, .insert l.wf⟩

/-- Returns `true` if the given key is present in the map. -/
@[inline]
def contains (l : DTreeMap α β cmp) (a : α) : Bool :=
  letI : Ord α := ⟨cmp⟩; l.inner.contains a

instance : Membership α (DTreeMap α β cmp) where
  mem m a := m.contains a

end DTreeMap

end Std
