/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.TreeSet.Basic
import Std.Data.TreeSet.Raw
import Std.Data.TreeMap.AdditionalOperations

/-!
# Additional tree set operations

This file defines more operations on `Std.TreeSet`.
We currently do not provide lemmas for these functions.
-/

set_option autoImplicit false
set_option linter.missingDocs true

universe u v w

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering}

namespace Std.TreeMap

/-!
We do not provide `get*GE`, `get*GT`, `get*LE` and `get*LT` functions for the raw trees.
-/

/--
Given a proof that such an element exists, retrieves the smallest element that is
greater than or equal to the given element.
-/
@[inline]
def getGE [TransCmp cmp] (t : TreeSet α cmp) (k : α) (h : ∃ a ∈ t, (cmp a k).isGE) : α :=
  TreeMap.getKeyGE t.inner k h

/--
Given a proof that such an element exists, retrieves the smallest element that is
greater than the given element.
-/
@[inline]
def getGT [TransCmp cmp] (t : TreeSet α cmp) (k : α) (h : ∃ a ∈ t, cmp a k = .gt) : α :=
  TreeMap.getKeyGT t.inner k h

/--
Given a proof that such an element exists, retrieves the largest element that is
less than or equal to the given element.
-/
@[inline]
def getLE [TransCmp cmp] (t : TreeSet α cmp) (k : α) (h : ∃ a ∈ t, (cmp a k).isLE) : α :=
  TreeMap.getKeyLE t.inner k h

/--
Given a proof that such an element exists, retrieves the smallest element that is
less than the given element.
-/
@[inline]
def getLT [TransCmp cmp] (t : TreeSet α cmp) (k : α) (h : ∃ a ∈ t, cmp a k = .lt) : α :=
  TreeMap.getKeyLT t.inner k h

end Std.TreeMap
