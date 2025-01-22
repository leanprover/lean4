/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Orderedtree.TreeMap.Raw

set_option autoImplicit false
set_option linter.missingDocs true

universe u v

variable {α : Type u} {cmp : α → α → Ordering}

namespace Std

namespace TreeSet

structure Raw (α : Type u) (cmp : α → α → Ordering) where
  /-- Internal implementation detail of the tree map. -/
  inner : TreeMap.Raw α Unit cmp

namespace Raw

structure WF (t : Raw α cmp) where
  /-- Internal implementation detail of the tree map. -/
  out : t.inner.WF

instance {t : Raw α cmp} : Coe t.WF t.inner.WF where
  coe t := t.out

@[inline]
def empty : Raw α cmp :=
  ⟨TreeMap.Raw.empty⟩

@[inline]
def isEmpty (t : Raw α cmp) : Bool :=
  t.inner.isEmpty

@[inline]
def insert (l : Raw α cmp) (a : α) : Raw α cmp :=
  ⟨l.inner.insert a ()⟩

@[inline]
def insertFast (l : Raw α cmp) (h : l.WF) (a : α) : Raw α cmp :=
  ⟨l.inner.insertFast h.out a ()⟩

@[inline]
def contains (l : Raw α cmp) (a : α) : Bool :=
  l.inner.contains a

instance : Membership α (Raw α cmp) where
  mem m a := m.contains a

end Raw

end TreeSet

end Std
