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
# Additional tree map operations

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

/-!
We do not provide `get*GE`, `get*GT`, `get*LE` and `get*LT` functions for the raw trees.
-/

end Raw

@[inline, inherit_doc DTreeMap.filterMap]
def filterMap (f : (a : α) → β → Option γ) (m : TreeMap α β cmp) : TreeMap α γ cmp :=
  ⟨m.inner.filterMap f⟩

@[inline, inherit_doc DTreeMap.map]
def map (f : α → β → γ) (t : TreeMap α β cmp) : TreeMap α γ cmp :=
  ⟨t.inner.map f⟩

@[inline, inherit_doc DTreeMap.Const.getEntryGE]
def getEntryGE [TransCmp cmp] (t : TreeMap α β cmp) (k : α) (h : ∃ a ∈ t, (cmp a k).isGE) :
    α × β :=
  DTreeMap.Const.getEntryGE t.inner k h

@[inline, inherit_doc DTreeMap.Const.getEntryGT]
def getEntryGT [TransCmp cmp] (t : TreeMap α β cmp) (k : α) (h : ∃ a ∈ t, cmp a k = .gt) :
    α × β :=
  DTreeMap.Const.getEntryGT t.inner k h

@[inline, inherit_doc DTreeMap.Const.getEntryLE]
def getEntryLE [TransCmp cmp] (t : TreeMap α β cmp) (k : α) (h : ∃ a ∈ t, (cmp a k).isLE) :
    α × β :=
  DTreeMap.Const.getEntryLE t.inner k h

@[inline, inherit_doc DTreeMap.Const.getEntryLT]
def getEntryLT [TransCmp cmp] (t : TreeMap α β cmp) (k : α) (h : ∃ a ∈ t, cmp a k = .lt) :
    α × β :=
  DTreeMap.Const.getEntryLT t.inner k h

@[inline, inherit_doc DTreeMap.getKeyGE]
def getKeyGE [TransCmp cmp] (t : TreeMap α β cmp) (k : α) (h : ∃ a ∈ t, (cmp a k).isGE) : α :=
  DTreeMap.getKeyGE t.inner k h

@[inline, inherit_doc DTreeMap.getKeyGT]
def getKeyGT [TransCmp cmp] (t : TreeMap α β cmp) (k : α) (h : ∃ a ∈ t, cmp a k = .gt) : α :=
  DTreeMap.getKeyGT t.inner k h

@[inline, inherit_doc DTreeMap.getKeyLE]
def getKeyLE [TransCmp cmp] (t : TreeMap α β cmp) (k : α) (h : ∃ a ∈ t, (cmp a k).isLE) : α :=
  DTreeMap.getKeyLE t.inner k h

@[inline, inherit_doc DTreeMap.getKeyLT]
def getKeyLT [TransCmp cmp] (t : TreeMap α β cmp) (k : α) (h : ∃ a ∈ t, cmp a k = .lt) : α :=
  DTreeMap.getKeyLT t.inner k h

end Std.TreeMap
