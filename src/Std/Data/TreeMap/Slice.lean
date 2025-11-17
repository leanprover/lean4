/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Std.Data.TreeMap.Raw.Slice
public import Std.Data.TreeMap.Basic

/-!
This module provides slice notation for `TreeMap` slices and implements an iterator
for those slices.
-/

namespace Std.TreeMap
open Std.Iterators

public instance {α : Type u} {β : Type v}
    (cmp : α → α → Ordering := by exact compare) :
    Rii.Sliceable (TreeMap α β cmp) α (DTreeMap.Internal.Const.RiiSlice α β) where
  mkSlice carrier range := ⟨carrier.inner.inner, range⟩

@[simp] public theorem toList_rii {α : Type u} {β : Type v}
    (cmp : α → α → Ordering := by exact compare) {t : TreeMap α β cmp} :
    t[*...*].toList = t.toList := by
  apply DTreeMap.Internal.Const.toList_rii

public instance {α : Type u} {β : Type v}
    (cmp : α → α → Ordering := by exact compare) :
    Ric.Sliceable (TreeMap α β cmp) α (@DTreeMap.Internal.Const.RicSlice α β ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner.inner, range⟩⟩

@[simp] public theorem toList_ric {α : Type u} {β : Type v}
    (cmp : α → α → Ordering := by exact compare) [TransCmp cmp]
    {t : TreeMap α β cmp} {bound : α} : t[*...=bound].toList =
      t.toList.filter (fun e => (cmp e.fst bound).isLE) :=
  @DTreeMap.Internal.Const.toList_ric α β ⟨cmp⟩ _ t.inner.inner (@t.inner.wf.ordered α (fun _ => β) ⟨cmp⟩ _) bound

public instance {α : Type u} {β : Type v} (cmp : α → α → Ordering := by exact compare) :
    Rio.Sliceable (TreeMap α β cmp) α (@DTreeMap.Internal.Const.RioSlice α β ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner.inner, range⟩⟩

@[simp] public theorem toList_rio {α : Type u} {β : Type v}
    (cmp : α → α → Ordering := by exact compare) [TransCmp cmp]
    {t : TreeMap α β cmp} {bound : α} : t[*...<bound].toList =
      t.toList.filter (fun e => (cmp e.fst bound).isLT) :=
  @DTreeMap.Internal.Const.toList_rio α β ⟨cmp⟩ _ t.inner.inner (@t.inner.wf.ordered α (fun _ => β) ⟨cmp⟩ _) bound

public instance {α : Type u} {β : Type v} (cmp : α → α → Ordering := by exact compare) :
    Rci.Sliceable (TreeMap α β cmp) α (@DTreeMap.Internal.Const.RciSlice α β ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner.inner, range⟩⟩

@[simp] public theorem toList_rci {α : Type u} {β : Type v} (cmp : α → α → Ordering := by exact compare)
    [TransCmp cmp] {t : TreeMap α β cmp} {bound : α} : t[bound...*].toList =
      t.toList.filter (fun e => (cmp e.fst bound).isGE) :=
  @DTreeMap.Internal.Const.toList_rci α β ⟨cmp⟩ _ t.inner.inner (@t.inner.wf.ordered α (fun _ => β) ⟨cmp⟩ _) bound

public instance {α : Type u} {β : Type v} (cmp : α → α → Ordering := by exact compare) :
    Rco.Sliceable (TreeMap α β cmp) α (@DTreeMap.Internal.Const.RcoSlice α β ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner.inner, range⟩⟩

@[simp] public theorem toList_rco {α : Type u} {β : Type v} (cmp : α → α → Ordering := by exact compare) [TransCmp cmp]
  {t : TreeMap α β cmp} {lowerBound upperBound : α} :
  t[lowerBound...<upperBound].toList =
    t.toList.filter (fun e => (cmp e.fst lowerBound).isGE ∧ (cmp e.fst upperBound).isLT) :=
  @DTreeMap.Internal.Const.toList_rco α β ⟨cmp⟩ _ t.inner.inner (@t.inner.wf.ordered α (fun _ => β) ⟨cmp⟩ _) lowerBound upperBound

public instance {α : Type u} {β : Type v} (cmp : α → α → Ordering := by exact compare) :
    Rcc.Sliceable (TreeMap α β cmp) α (@DTreeMap.Internal.Const.RccSlice α β ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner.inner, range⟩⟩

@[simp] public theorem toList_rcc {α : Type u} {β : Type v}
    (cmp : α → α → Ordering := by exact compare)  [TransCmp cmp]
    {t : TreeMap α β cmp} {lowerBound upperBound : α} : t[lowerBound...=upperBound].toList =
    t.toList.filter (fun e => (cmp e.fst lowerBound).isGE ∧ (cmp e.fst upperBound).isLE) :=
  @DTreeMap.Internal.Const.toList_rcc α β ⟨cmp⟩ _ t.inner.inner (@t.inner.wf.ordered α (fun _ => β) ⟨cmp⟩ _) lowerBound upperBound

public instance {α : Type u} {β : Type v} (cmp : α → α → Ordering := by exact compare) :
    Roi.Sliceable (TreeMap α β cmp) α (@DTreeMap.Internal.Const.RoiSlice α β ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner.inner, range⟩⟩

@[simp] public theorem toList_roi {α : Type u} {β : Type v}
    (cmp : α → α → Ordering := by exact compare) [TransCmp cmp]
    {t : TreeMap α β cmp} {bound : α} : t[bound<...*].toList =
      t.toList.filter (fun e => (cmp e.fst bound).isGT) :=
  @DTreeMap.Internal.Const.toList_roi α β ⟨cmp⟩ _ t.inner.inner (@t.inner.wf.ordered α (fun _ => β) ⟨cmp⟩ _) bound

public instance {α : Type u} {β : Type v} (cmp : α → α → Ordering := by exact compare) :
    Roc.Sliceable (TreeMap α β cmp) α (@DTreeMap.Internal.Const.RocSlice α β ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner.inner, range⟩⟩

@[simp] public theorem toList_roc {α : Type u} {β : Type v}
    (cmp : α → α → Ordering := by exact compare) [TransCmp cmp]
    {t : TreeMap α β cmp} {lowerBound upperBound : α} :
    t[lowerBound<...=upperBound].toList =
      t.toList.filter (fun e => (cmp e.fst lowerBound).isGT ∧ (cmp e.fst upperBound).isLE) :=
  @DTreeMap.Internal.Const.toList_roc α β ⟨cmp⟩ _ t.inner.inner (@t.inner.wf.ordered α (fun _ => β) ⟨cmp⟩ _) lowerBound upperBound

public instance {α : Type u} {β : Type v} (cmp : α → α → Ordering := by exact compare) :
    Roo.Sliceable (TreeMap α β cmp) α (@DTreeMap.Internal.Const.RooSlice α β ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner.inner, range⟩⟩

@[simp] public theorem toList_roo {α : Type u} {β : Type v}
    (cmp : α → α → Ordering := by exact compare) [TransCmp cmp]
    {t : TreeMap α β cmp} {lowerBound upperBound : α} : t[lowerBound<...upperBound].toList =
      t.toList.filter (fun e => (cmp e.fst lowerBound).isGT ∧ (cmp e.fst upperBound).isLT) :=
  @DTreeMap.Internal.Const.toList_roo α β ⟨cmp⟩ _ t.inner.inner (@t.inner.wf.ordered α (fun _ => β) ⟨cmp⟩ _) lowerBound upperBound

end Std.TreeMap
