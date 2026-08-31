/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Std.Data.TreeMap.Raw.Slice
public import Std.Data.TreeSet.Raw.Basic

/-!
This module provides slice notation for `TreeSet` slices and implements an iterator
for those slices.
-/

namespace Std.TreeSet.Raw
open Std.Iterators

public instance {α : Type u}
    (cmp : α → α → Ordering := by exact compare) :
    Rii.Sliceable (Raw α cmp) α (DTreeMap.Internal.Unit.RiiSlice α) where
  mkSlice carrier range := ⟨carrier.inner.inner.inner, range⟩

@[simp] public theorem toList_rii {α : Type u}
    (cmp : α → α → Ordering := by exact compare) {t : Raw α cmp} :
    t[*...*].toList = t.toList := by
  apply DTreeMap.Internal.Unit.toList_rii

public instance {α : Type u} (cmp : α → α → Ordering := by exact compare) :
    Ric.Sliceable (Raw α cmp) α (@DTreeMap.Internal.Unit.RicSlice α ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner.inner.inner, range⟩⟩

public theorem toList_ric {α : Type u} (cmp : α → α → Ordering := by exact compare)
    [TransCmp cmp] {t : Raw α cmp} (wf : t.WF) {bound : α} :
    t[*...=bound].toList = t.toList.filter (fun e => (cmp e bound).isLE) := by
  apply @DTreeMap.Internal.Unit.toList_ric _ ⟨cmp⟩ _ _
  · exact @wf.out.out.out.ordered _ _ ⟨cmp⟩ _

public instance {α : Type u} (cmp : α → α → Ordering := by exact compare) :
    Rio.Sliceable (Raw α cmp) α (@DTreeMap.Internal.Unit.RioSlice α ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner.inner.inner, range⟩⟩

public theorem toList_rio {α : Type u} (cmp : α → α → Ordering := by exact compare)
    [TransCmp cmp] {t : Raw α cmp} (wf : t.WF) {bound : α} :
    t[*...<bound].toList = t.toList.filter (fun e => (cmp e bound).isLT) := by
  apply @DTreeMap.Internal.Unit.toList_rio _ ⟨cmp⟩ _ _
  · exact @wf.out.out.out.ordered _ _ ⟨cmp⟩ _

public instance {α : Type u} (cmp : α → α → Ordering := by exact compare) :
    Rci.Sliceable (Raw α cmp) α (@DTreeMap.Internal.Unit.RciSlice α ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner.inner.inner, range⟩⟩

public theorem toList_rci {α : Type u} (cmp : α → α → Ordering := by exact compare)
    [TransCmp cmp] {t : Raw α cmp} (wf : t.WF) {bound : α} :
    t[bound...*].toList = t.toList.filter (fun e => (cmp e bound).isGE) := by
  apply @DTreeMap.Internal.Unit.toList_rci _ ⟨cmp⟩ _ _
  · exact @wf.out.out.out.ordered _ _ ⟨cmp⟩ _

public instance {α : Type u} (cmp : α → α → Ordering := by exact compare) :
    Rco.Sliceable (Raw α cmp) α (@DTreeMap.Internal.Unit.RcoSlice α ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner.inner.inner, range⟩⟩

public theorem toList_rco {α : Type u} (cmp : α → α → Ordering := by exact compare)
    [TransCmp cmp] {t : Raw α cmp} (wf : t.WF) {lowerBound upperBound : α} :
    t[lowerBound...<upperBound].toList =
      t.toList.filter (fun e => (cmp e lowerBound).isGE ∧ (cmp e upperBound).isLT) := by
  apply @DTreeMap.Internal.Unit.toList_rco _ ⟨cmp⟩ _ _
  · exact @wf.out.out.out.ordered _ _ ⟨cmp⟩ _

public instance {α : Type u} (cmp : α → α → Ordering := by exact compare) :
    Rcc.Sliceable (Raw α cmp) α (@DTreeMap.Internal.Unit.RccSlice α ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner.inner.inner, range⟩⟩

public theorem toList_rcc {α : Type u} (cmp : α → α → Ordering := by exact compare)
    [TransCmp cmp] {t : Raw α cmp} (wf : t.WF) {lowerBound upperBound : α} :
    t[lowerBound...=upperBound].toList =
      t.toList.filter (fun e => (cmp e lowerBound).isGE ∧ (cmp e upperBound).isLE) := by
  apply @DTreeMap.Internal.Unit.toList_rcc _ ⟨cmp⟩ _ _
  · exact @wf.out.out.out.ordered _ _ ⟨cmp⟩ _

public instance {α : Type u} (cmp : α → α → Ordering := by exact compare) :
    Roi.Sliceable (Raw α cmp) α (@DTreeMap.Internal.Unit.RoiSlice α ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner.inner.inner, range⟩⟩

public theorem toList_roi {α : Type u} (cmp : α → α → Ordering := by exact compare)
    [TransCmp cmp] {t : Raw α cmp} (wf : t.WF) {bound: α} : t[bound<...*].toList =
      t.toList.filter (fun e => (cmp e bound).isGT) := by
  apply @DTreeMap.Internal.Unit.toList_roi _ ⟨cmp⟩ _
  · exact @wf.out.out.out.ordered _ _ ⟨cmp⟩ _

public instance {α : Type u} (cmp : α → α → Ordering := by exact compare) :
    Roc.Sliceable (Raw α cmp) α (@DTreeMap.Internal.Unit.RocSlice α ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner.inner.inner, range⟩⟩

public theorem toList_roc {α : Type u} (cmp : α → α → Ordering := by exact compare)
    [TransCmp cmp] {t : Raw α cmp} (wf : t.WF) {lowerBound upperBound : α} :
    t[lowerBound<...=upperBound].toList =
      t.toList.filter (fun e => (cmp e lowerBound).isGT ∧ (cmp e upperBound).isLE) := by
  apply @DTreeMap.Internal.Unit.toList_roc _  ⟨cmp⟩ _
  · exact @wf.out.out.out.ordered _ _ ⟨cmp⟩ _

public instance {α : Type u} (cmp : α → α → Ordering := by exact compare) :
    Roo.Sliceable (Raw α cmp) α (@DTreeMap.Internal.Unit.RooSlice α ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner.inner.inner, range⟩⟩

public theorem toList_roo {α : Type u} (cmp : α → α → Ordering := by exact compare)
    [TransCmp cmp] {t : Raw α cmp} (wf : t.WF) {lowerBound upperBound : α} :
    t[lowerBound<...upperBound].toList =
      t.toList.filter (fun e => (cmp e lowerBound).isGT ∧ (cmp e upperBound).isLT) := by
  apply @DTreeMap.Internal.Unit.toList_roo _ ⟨cmp⟩ _
  · exact @wf.out.out.out.ordered _ _ ⟨cmp⟩ _

end Std.TreeSet.Raw
