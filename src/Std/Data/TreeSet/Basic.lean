/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Orderedtree.TreeMap.Basic

set_option autoImplicit false
set_option linter.missingDocs true

universe u v

variable {α : Type u} {cmp : α → α → Ordering}

namespace Std

structure TreeSet (α : Type u) (cmp : α → α → Ordering) where
  /-- Internal implementation detail of the tree map. -/
  inner : TreeMap α Unit cmp

namespace TreeSet

@[inline]
def empty : TreeSet α cmp :=
  ⟨TreeMap.empty⟩

@[inline]
def isEmpty (t : TreeSet α cmp) : Bool :=
  t.inner.isEmpty

@[inline]
def insert (l : TreeSet α cmp) (a : α) : TreeSet α cmp :=
  ⟨l.inner.insert a ()⟩

@[inline]
def contains (l : TreeSet α cmp) (a : α) : Bool :=
  l.inner.contains a

instance : Membership α (TreeSet α cmp) where
  mem m a := m.contains a

end TreeSet

end Std
