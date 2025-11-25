/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Std.Data.DTreeMap.Raw.Slice

/-!
This module provides slice notation for `TreeMap` slices and implements an iterator
for those slices.
-/

namespace Std.DTreeMap
open Std.Iterators

public instance {α : Type u} {β : α → Type v}
    (cmp : α → α → Ordering := by exact compare) :
    Rii.Sliceable (DTreeMap α β cmp) α (Internal.RiiSlice α β) where
  mkSlice carrier range := ⟨carrier.inner, range⟩

@[simp] public theorem toList_rii {α : Type u} {β : α → Type v}
    (cmp : α → α → Ordering := by exact compare) {t : DTreeMap α β cmp} :
    t[*...*].toList = t.toList := by
  apply Internal.toList_rii

public instance {α : Type u} {β : α → Type v}
    (cmp : α → α → Ordering := by exact compare) :
    Ric.Sliceable (DTreeMap α β cmp) α (@Internal.RicSlice α β ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner, range⟩⟩

@[simp] public theorem toList_ric {α : Type u} {β : α → Type v}
    (cmp : α → α → Ordering := by exact compare) [TransCmp cmp]
    {t : DTreeMap α β cmp} {bound : α} : t[*...=bound].toList =
      t.toList.filter (fun e => (cmp e.fst bound).isLE) :=
  @Internal.toList_ric α β ⟨cmp⟩ _ t.inner (@t.wf.ordered α β ⟨cmp⟩ _) bound

public instance {α : Type u} {β : α → Type v} (cmp : α → α → Ordering := by exact compare) :
    Rio.Sliceable (DTreeMap α β cmp) α (@Internal.RioSlice α β ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner, range⟩⟩

@[simp] public theorem toList_rio {α : Type u} {β : α → Type v}
    (cmp : α → α → Ordering := by exact compare) [TransCmp cmp]
    {t : DTreeMap α β cmp} {bound : α} : t[*...<bound].toList =
      t.toList.filter (fun e => (cmp e.fst bound).isLT) :=
  @Internal.toList_rio α β ⟨cmp⟩ _ t.inner (@t.wf.ordered α β ⟨cmp⟩ _) bound

public instance {α : Type u} {β : α → Type v} (cmp : α → α → Ordering := by exact compare) :
    Rci.Sliceable (DTreeMap α β cmp) α (@Internal.RciSlice α β ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner, range⟩⟩

@[simp] public theorem toList_rci {α : Type u} {β : α → Type v} (cmp : α → α → Ordering := by exact compare)
    [TransCmp cmp] {t : DTreeMap α β cmp} {bound : α} : t[bound...*].toList =
      t.toList.filter (fun e => (cmp e.fst bound).isGE) :=
  @Internal.toList_rci α β ⟨cmp⟩ _ t.inner (@t.wf.ordered α β ⟨cmp⟩ _) bound

public instance {α : Type u} {β : α → Type v} (cmp : α → α → Ordering := by exact compare) :
    Rco.Sliceable (DTreeMap α β cmp) α (@Internal.RcoSlice α β ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner, range⟩⟩

@[simp] public theorem toList_rco {α : Type u} {β : α → Type v} (cmp : α → α → Ordering := by exact compare) [TransCmp cmp]
  {t : DTreeMap α β cmp} {lowerBound upperBound : α} :
  t[lowerBound...<upperBound].toList =
    t.toList.filter (fun e => (cmp e.fst lowerBound).isGE ∧ (cmp e.fst upperBound).isLT) :=
  @Internal.toList_rco α β ⟨cmp⟩ _ t.inner (@t.wf.ordered α β ⟨cmp⟩ _) lowerBound upperBound

public instance {α : Type u} {β : α → Type v} (cmp : α → α → Ordering := by exact compare) :
    Rcc.Sliceable (DTreeMap α β cmp) α (@Internal.RccSlice α β ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner, range⟩⟩

@[simp] public theorem toList_rcc {α : Type u} {β : α → Type v}
    (cmp : α → α → Ordering := by exact compare)  [TransCmp cmp]
    {t : DTreeMap α β cmp} {lowerBound upperBound : α} : t[lowerBound...=upperBound].toList =
    t.toList.filter (fun e => (cmp e.fst lowerBound).isGE ∧ (cmp e.fst upperBound).isLE) :=
  @Internal.toList_rcc α β ⟨cmp⟩ _ t.inner (@t.wf.ordered α β ⟨cmp⟩ _) lowerBound upperBound

public instance {α : Type u} {β : α → Type v} (cmp : α → α → Ordering := by exact compare) :
    Roi.Sliceable (DTreeMap α β cmp) α (@Internal.RoiSlice α β ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner, range⟩⟩

@[simp] public theorem toList_roi {α : Type u} {β : α → Type v}
    (cmp : α → α → Ordering := by exact compare) [TransCmp cmp]
    {t : DTreeMap α β cmp} {bound : α} : t[bound<...*].toList =
      t.toList.filter (fun e => (cmp e.fst bound).isGT) :=
  @Internal.toList_roi α β ⟨cmp⟩ _ t.inner (@t.wf.ordered α β ⟨cmp⟩ _) bound

public instance {α : Type u} {β : α → Type v} (cmp : α → α → Ordering := by exact compare) :
    Roc.Sliceable (DTreeMap α β cmp) α (@Internal.RocSlice α β ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner, range⟩⟩

@[simp] public theorem toList_roc {α : Type u} {β : α → Type v}
    (cmp : α → α → Ordering := by exact compare) [TransCmp cmp]
    {t : DTreeMap α β cmp} {lowerBound upperBound : α} :
    t[lowerBound<...=upperBound].toList =
      t.toList.filter (fun e => (cmp e.fst lowerBound).isGT ∧ (cmp e.fst upperBound).isLE) :=
  @Internal.toList_roc α β ⟨cmp⟩ _ t.inner (@t.wf.ordered α β ⟨cmp⟩ _) lowerBound upperBound

public instance {α : Type u} {β : α → Type v} (cmp : α → α → Ordering := by exact compare) :
    Roo.Sliceable (DTreeMap α β cmp) α (@Internal.RooSlice α β ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner, range⟩⟩

@[simp] public theorem toList_roo {α : Type u} {β : α → Type v}
    (cmp : α → α → Ordering := by exact compare) [TransCmp cmp]
    {t : DTreeMap α β cmp} {lowerBound upperBound : α} : t[lowerBound<...upperBound].toList =
      t.toList.filter (fun e => (cmp e.fst lowerBound).isGT ∧ (cmp e.fst upperBound).isLT) :=
  @Internal.toList_roo α β ⟨cmp⟩ _ t.inner (@t.wf.ordered α β ⟨cmp⟩ _) lowerBound upperBound

end Std.DTreeMap
