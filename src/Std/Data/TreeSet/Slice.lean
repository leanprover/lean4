/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Std.Data.TreeSet.Raw.Slice

/-!
This module provides slice notation for `TreeSet` slices and implements an iterator
for those slices.
-/

namespace Std.TreeSet
open Std.Iterators

public instance {α : Type u}
    (cmp : α → α → Ordering := by exact compare) :
    Rii.Sliceable (TreeSet α cmp) α (DTreeMap.Internal.Unit.RiiSlice α) where
  mkSlice carrier range := ⟨carrier.inner.inner.inner, range⟩

@[simp] public theorem toList_rii {α : Type u}
    (cmp : α → α → Ordering := by exact compare) {t : TreeSet α cmp} :
    t[*...*].toList = t.toList := by
  apply DTreeMap.Internal.Unit.toList_rii

public instance {α : Type u}
    (cmp : α → α → Ordering := by exact compare) :
    Ric.Sliceable (TreeSet α cmp) α (@DTreeMap.Internal.Unit.RicSlice α ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner.inner.inner, range⟩⟩

@[simp] public theorem toList_ric {α : Type u}
    (cmp : α → α → Ordering := by exact compare) [TransCmp cmp]
    {t : TreeSet α cmp} {bound : α} : t[*...=bound].toList =
      t.toList.filter (fun e => (cmp e bound).isLE) :=
  @DTreeMap.Internal.Unit.toList_ric α ⟨cmp⟩ _ t.inner.inner.inner (@t.inner.inner.wf.ordered α (fun _ => Unit) ⟨cmp⟩ _) bound

public instance {α : Type u} (cmp : α → α → Ordering := by exact compare) :
    Rio.Sliceable (TreeSet α cmp) α (@DTreeMap.Internal.Unit.RioSlice α ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner.inner.inner, range⟩⟩

@[simp] public theorem toList_rio {α : Type u}
    (cmp : α → α → Ordering := by exact compare) [TransCmp cmp]
    {t : TreeSet α cmp} {bound : α} : t[*...<bound].toList =
      t.toList.filter (fun e => (cmp e bound).isLT) :=
  @DTreeMap.Internal.Unit.toList_rio α ⟨cmp⟩ _ t.inner.inner.inner (@t.inner.inner.wf.ordered α (fun _ => Unit) ⟨cmp⟩ _) bound

public instance {α : Type u} (cmp : α → α → Ordering := by exact compare) :
    Rci.Sliceable (TreeSet α cmp) α (@DTreeMap.Internal.Unit.RciSlice α ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner.inner.inner, range⟩⟩

@[simp] public theorem toList_rci {α : Type u} (cmp : α → α → Ordering := by exact compare)
    [TransCmp cmp] {t : TreeSet α cmp} {bound : α} : t[bound...*].toList =
      t.toList.filter (fun e => (cmp e bound).isGE) :=
  @DTreeMap.Internal.Unit.toList_rci α ⟨cmp⟩ _ t.inner.inner.inner (@t.inner.inner.wf.ordered α (fun _ => Unit) ⟨cmp⟩ _) bound

public instance {α : Type u} (cmp : α → α → Ordering := by exact compare) :
    Rco.Sliceable (TreeSet α cmp) α (@DTreeMap.Internal.Unit.RcoSlice α ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner.inner.inner, range⟩⟩

@[simp] public theorem toList_rco {α : Type u} (cmp : α → α → Ordering := by exact compare) [TransCmp cmp]
  {t : TreeSet α cmp} {lowerBound upperBound : α} :
  t[lowerBound...<upperBound].toList =
    t.toList.filter (fun e => (cmp e lowerBound).isGE ∧ (cmp e upperBound).isLT) :=
  @DTreeMap.Internal.Unit.toList_rco α ⟨cmp⟩ _ t.inner.inner.inner (@t.inner.inner.wf.ordered α (fun _ => Unit) ⟨cmp⟩ _) lowerBound upperBound

public instance {α : Type u} (cmp : α → α → Ordering := by exact compare) :
    Rcc.Sliceable (TreeSet α cmp) α (@DTreeMap.Internal.Unit.RccSlice α ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner.inner.inner, range⟩⟩

@[simp] public theorem toList_rcc {α : Type u}
    (cmp : α → α → Ordering := by exact compare)  [TransCmp cmp]
    {t : TreeSet α cmp} {lowerBound upperBound : α} : t[lowerBound...=upperBound].toList =
    t.toList.filter (fun e => (cmp e lowerBound).isGE ∧ (cmp e upperBound).isLE) :=
  @DTreeMap.Internal.Unit.toList_rcc α ⟨cmp⟩ _ t.inner.inner.inner (@t.inner.inner.wf.ordered α (fun _ => Unit) ⟨cmp⟩ _) lowerBound upperBound

public instance {α : Type u} (cmp : α → α → Ordering := by exact compare) :
    Roi.Sliceable (TreeSet α cmp) α (@DTreeMap.Internal.Unit.RoiSlice α ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner.inner.inner, range⟩⟩

@[simp] public theorem toList_roi {α : Type u}
    (cmp : α → α → Ordering := by exact compare) [TransCmp cmp]
    {t : TreeSet α cmp} {bound : α} : t[bound<...*].toList =
      t.toList.filter (fun e => (cmp e bound).isGT) :=
  @DTreeMap.Internal.Unit.toList_roi α ⟨cmp⟩ _ t.inner.inner.inner (@t.inner.inner.wf.ordered α (fun _ => Unit) ⟨cmp⟩ _) bound

public instance {α : Type u} (cmp : α → α → Ordering := by exact compare) :
    Roc.Sliceable (TreeSet α cmp) α (@DTreeMap.Internal.Unit.RocSlice α ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner.inner.inner, range⟩⟩

@[simp] public theorem toList_roc {α : Type u}
    (cmp : α → α → Ordering := by exact compare) [TransCmp cmp]
    {t : TreeSet α cmp} {lowerBound upperBound : α} :
    t[lowerBound<...=upperBound].toList =
      t.toList.filter (fun e => (cmp e lowerBound).isGT ∧ (cmp e upperBound).isLE) :=
  @DTreeMap.Internal.Unit.toList_roc α ⟨cmp⟩ _ t.inner.inner.inner (@t.inner.inner.wf.ordered α (fun _ => Unit) ⟨cmp⟩ _) lowerBound upperBound

public instance {α : Type u} (cmp : α → α → Ordering := by exact compare) :
    Roo.Sliceable (TreeSet α cmp) α (@DTreeMap.Internal.Unit.RooSlice α ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner.inner.inner, range⟩⟩

@[simp] public theorem toList_roo {α : Type u}
    (cmp : α → α → Ordering := by exact compare) [TransCmp cmp]
    {t : TreeSet α cmp} {lowerBound upperBound : α} : t[lowerBound<...upperBound].toList =
      t.toList.filter (fun e => (cmp e lowerBound).isGT ∧ (cmp e upperBound).isLT) :=
  @DTreeMap.Internal.Unit.toList_roo α ⟨cmp⟩ _ t.inner.inner.inner (@t.inner.inner.wf.ordered α (fun _ => Unit) ⟨cmp⟩ _) lowerBound upperBound

end Std.TreeSet
