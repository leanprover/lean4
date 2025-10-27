/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Std.Data.DTreeMap.Internal.Ordered
public import Std.Data.DTreeMap.Internal.Zipper
public import Std.Data.DTreeMap.Raw.Basic

namespace Std.DTreeMap.Raw
open Std.Iterators

public instance {α : Type u} {β : α → Type v}
    (cmp : α → α → Ordering := by exact compare) :
    Rii.Sliceable (Raw α β cmp) α (Internal.RiiSlice α β) where
  mkSlice carrier range := ⟨carrier.inner, range⟩

@[simp] public theorem toList_rii {α : Type u} {β : α → Type v}
    [Ord α] {t : Raw α β compare} : t[*...*].toList = t.toList := by
  apply Internal.toList_rii

public instance {α : Type u} {β : α → Type v} [Ord α] (cmp : α → α → Ordering := by exact compare) :
    Ric.Sliceable (Raw α β cmp) α (Internal.RicSlice α β) where
  mkSlice carrier range := ⟨carrier.inner, range⟩

public theorem toList_ric {α : Type u} {β : α → Type v} [Ord α] [TransOrd α]
    {t : Raw α β compare} {wf : t.WF} {bound : α} :
    t[*...=bound].toList = t.toList.filter (fun e => (compare e.fst bound).isLE) := by
  apply Internal.toList_ric
  . exact wf.out.ordered

public instance {α : Type u} {β : α → Type v} [Ord α] (cmp : α → α → Ordering := by exact compare) :
    Rio.Sliceable (Raw α β cmp) α (Internal.RioSlice α β) where
  mkSlice carrier range := ⟨carrier.inner, range⟩

public theorem toList_rio {α : Type u} {β : α → Type v} [Ord α] [TransOrd α] {t : Raw α β compare} {wf : t.WF} {bound : α} :
    t[*...<bound].toList = t.toList.filter (fun e => (compare e.fst bound).isLT) := by
  apply Internal.toList_rio
  . exact wf.out.ordered

public instance {α : Type u} {β : α → Type v} [Ord α] (cmp : α → α → Ordering := by exact compare) :
    Rci.Sliceable (Raw α β cmp) α (Internal.RciSlice α β) where
  mkSlice carrier range := ⟨carrier.inner, range⟩

public theorem toList_rci {α : Type u} {β : α → Type v} [Ord α] [TransOrd α] {t : Raw α β compare} {wf : t.WF} {bound : α} :
    t[bound...*].toList = t.toList.filter (fun e => (compare e.fst bound).isGE) := by
  apply Internal.toList_rci
  . exact wf.out.ordered

public instance {α : Type u} {β : α → Type v} [Ord α] (cmp : α → α → Ordering := by exact compare) :
    Rco.Sliceable (Raw α β cmp) α (Internal.RcoSlice α β) where
  mkSlice carrier range := ⟨carrier.inner, range⟩

public theorem toList_rco {α : Type u} {β : α → Type v} [Ord α] [TransOrd α] {t : Raw α β compare}
    {wf : t.WF} {lowerBound upperBound : α} : t[lowerBound...<upperBound].toList =
      t.toList.filter (fun e => (compare e.fst lowerBound).isGE ∧ (compare e.fst upperBound).isLT) := by
  apply Internal.toList_rco
  . exact wf.out.ordered

public instance {α : Type u} {β : α → Type v} [Ord α] (cmp : α → α → Ordering := by exact compare) :
    Rcc.Sliceable (Raw α β cmp) α (Internal.RccSlice α β) where
  mkSlice carrier range := ⟨carrier.inner, range⟩

public theorem toList_rcc {α : Type u} {β : α → Type v} [Ord α] [TransOrd α] {t : Raw α β compare}
    {wf : t.WF} {lowerBound upperBound : α} : t[lowerBound...=upperBound].toList =
      t.toList.filter (fun e => (compare e.fst lowerBound).isGE ∧ (compare e.fst upperBound).isLE) := by
  apply Internal.toList_rcc
  . exact wf.out.ordered

public instance {α : Type u} {β : α → Type v} [Ord α] (cmp : α → α → Ordering := by exact compare) :
    Roi.Sliceable (Raw α β cmp) α (Internal.RoiSlice α β) where
  mkSlice carrier range := ⟨carrier.inner, range⟩

public theorem toList_roi {α : Type u} {β : α → Type v} [Ord α] [TransOrd α]
    {t : Raw α β compare} {wf : t.WF} {bound: α} : t[bound<...*].toList =
      t.toList.filter (fun e => (compare e.fst bound).isGT) := by
  apply Internal.toList_roi
  . exact wf.out.ordered

public instance {α : Type u} {β : α → Type v} [Ord α] (cmp : α → α → Ordering := by exact compare) :
    Roc.Sliceable (Raw α β cmp) α (Internal.RocSlice α β) where
  mkSlice carrier range := ⟨carrier.inner, range⟩

public theorem toList_roc {α : Type u} {β : α → Type v} [Ord α] [TransOrd α] {t : Raw α β compare}
    {wf : t.WF} {lowerBound upperBound : α} : t[lowerBound<...=upperBound].toList =
      t.toList.filter (fun e => (compare e.fst lowerBound).isGT ∧ (compare e.fst upperBound).isLE) := by
  apply Internal.toList_roc
  . exact wf.out.ordered

public instance {α : Type u} {β : α → Type v} [Ord α] (cmp : α → α → Ordering := by exact compare) :
    Roo.Sliceable (Raw α β cmp) α (Internal.RooSlice α β) where
  mkSlice carrier range := ⟨carrier.inner, range⟩

public theorem toList_roo {α : Type u} {β : α → Type v} [Ord α] [TransOrd α]
    {t : Raw α β compare} {wf : t.WF} {lowerBound upperBound : α} : t[lowerBound<...upperBound].toList =
      t.toList.filter (fun e => (compare e.fst lowerBound).isGT ∧ (compare e.fst upperBound).isLT) := by
  apply Internal.toList_roo
  . exact wf.out.ordered

end Std.DTreeMap.Raw
