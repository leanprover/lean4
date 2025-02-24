/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.DTreeMap.Raw
import Std.Data.DTreeMap.Internal.WF.Lemmas

/-!
# Additional dependent tree map operations

This file defines more operations on `Std.DTreeMap`.
We currently do not provide lemmas for these functions.
-/

set_option autoImplicit false
set_option linter.missingDocs true

universe u v w

variable {α : Type u} {β : α → Type v} {γ : α → Type w} {cmp : α → α → Ordering}
private local instance : Coe (Type v) (α → Type v) where coe γ := fun _ => γ

namespace Std.DTreeMap
open Internal (Impl)

namespace Raw

/--
Updates the values of the map by applying the given function to all mappings, keeping
only those mappings where the function returns `some` value.
-/
def filterMap (f : (a : α) → β a → Option (γ a)) (t : Raw α β cmp) : Raw α γ cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.filterMap! f⟩

/-- Updates the values of the map by applying the given function to all mappings. -/
@[inline]
def map (f : (a : α) → β a → γ a) (t : Raw α β cmp) : Raw α γ cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.map f⟩

/-!
We do not provide `get*GE`, `get*GT`, `get*LE` and `get*LT` functions for the raw trees.
-/

end Raw

@[inline, inherit_doc Raw.filterMap]
def filterMap (f : (a : α) → β a → Option (γ a)) (t : DTreeMap α β cmp) : DTreeMap α γ cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.filterMap f t.wf.balanced |>.impl, t.wf.filterMap⟩

@[inline, inherit_doc Raw.map]
def map (f : (a : α) → β a → γ a) (t : DTreeMap α β cmp) : DTreeMap α γ cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.map f, t.wf.map⟩

/--
Given a proof that such a mapping exists, retrieves the key-value pair with the smallest key that is
greater than or equal to the given key.
-/
@[inline]
def getEntryGE [TransCmp cmp] (t : DTreeMap α β cmp) (k : α) (h : ∃ a ∈ t, (cmp a k).isGE) :
    (a : α) × β a :=
  letI : Ord α := ⟨cmp⟩; Impl.getEntryGE k t.inner t.wf.ordered h

/--
Given a proof that such a mapping exists, retrieves the key-value pair with the smallest key that is
greater than the given key.
-/
@[inline]
def getEntryGT [TransCmp cmp] (t : DTreeMap α β cmp) (k : α) (h : ∃ a ∈ t, cmp a k = .gt) :
    (a : α) × β a :=
  letI : Ord α := ⟨cmp⟩; Impl.getEntryGT k t.inner t.wf.ordered h

/--
Given a proof that such a mapping exists, retrieves the key-value pair with the largest key that is
less than or equal to the given key.
-/
@[inline]
def getEntryLE [TransCmp cmp] (t : DTreeMap α β cmp) (k : α) (h : ∃ a ∈ t, (cmp a k).isLE) :
    (a : α) × β a :=
  letI : Ord α := ⟨cmp⟩; Impl.getEntryLE k t.inner t.wf.ordered h

/--
Given a proof that such a mapping exists, retrieves the key-value pair with the smallest key that is
less than the given key.
-/
@[inline]
def getEntryLT [TransCmp cmp] (t : DTreeMap α β cmp) (k : α) (h : ∃ a ∈ t, cmp a k = .lt) :
    (a : α) × β a :=
  letI : Ord α := ⟨cmp⟩; Impl.getEntryLT k t.inner t.wf.ordered h

/--
Given a proof that such a mapping exists, retrieves the smallest key that is
greater than or equal to the given key.
-/
@[inline]
def getKeyGE [TransCmp cmp] (t : DTreeMap α β cmp) (k : α) (h : ∃ a ∈ t, (cmp a k).isGE) : α :=
  letI : Ord α := ⟨cmp⟩; Impl.getKeyGE k t.inner t.wf.ordered h

/--
Given a proof that such a mapping exists, retrieves the smallest key that is
greater than the given key.
-/
@[inline]
def getKeyGT [TransCmp cmp] (t : DTreeMap α β cmp) (k : α) (h : ∃ a ∈ t, cmp a k = .gt) : α :=
  letI : Ord α := ⟨cmp⟩; Impl.getKeyGT k t.inner t.wf.ordered h

/--
Given a proof that such a mapping exists, retrieves the largest key that is
less than or equal to the given key.
-/
@[inline]
def getKeyLE [TransCmp cmp] (t : DTreeMap α β cmp) (k : α) (h : ∃ a ∈ t, (cmp a k).isLE) : α :=
  letI : Ord α := ⟨cmp⟩; Impl.getKeyLE k t.inner t.wf.ordered h

/--
Given a proof that such a mapping exists, retrieves the smallest key that is
less than the given key.
-/
@[inline]
def getKeyLT [TransCmp cmp] (t : DTreeMap α β cmp) (k : α) (h : ∃ a ∈ t, cmp a k = .lt) : α :=
  letI : Ord α := ⟨cmp⟩; Impl.getKeyLT k t.inner t.wf.ordered h

namespace Const

variable {β : Type v}

/--
Given a proof that such a mapping exists, retrieves the key-value pair with the smallest key that is
greater than or equal to the given key.
-/
@[inline]
def getEntryGE [TransCmp cmp] (t : DTreeMap α β cmp) (k : α) (h : ∃ a ∈ t, (cmp a k).isGE) :
    α × β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.getEntryGE k t.inner t.wf.ordered h

/--
Given a proof that such a mapping exists, retrieves the key-value pair with the smallest key that is
greater than the given key.
-/
@[inline]
def getEntryGT [TransCmp cmp] (t : DTreeMap α β cmp) (k : α) (h : ∃ a ∈ t, cmp a k = .gt) :
    α × β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.getEntryGT k t.inner t.wf.ordered h

/--
Given a proof that such a mapping exists, retrieves the key-value pair with the largest key that is
less than or equal to the given key.
-/
@[inline]
def getEntryLE [TransCmp cmp] (t : DTreeMap α β cmp) (k : α) (h : ∃ a ∈ t, (cmp a k).isLE) :
    α × β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.getEntryLE k t.inner t.wf.ordered h

/--
Given a proof that such a mapping exists, retrieves the key-value pair with the smallest key that is
less than the given key.
-/
@[inline]
def getEntryLT [TransCmp cmp] (t : DTreeMap α β cmp) (k : α) (h : ∃ a ∈ t, cmp a k = .lt) :
    α × β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.getEntryLT k t.inner t.wf.ordered h

end Const

end Std.DTreeMap
