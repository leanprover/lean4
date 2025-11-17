/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Std.Data.DTreeMap.Raw.Slice
public import Std.Data.TreeMap.Raw.Basic

/-!
This module provides slice notation for `TreeMap` slices and implements an iterator
for those slices.
-/

namespace Std.TreeMap.Raw
open Std.Iterators

public instance {α : Type u} {β : Type v}
    (cmp : α → α → Ordering := by exact compare) :
    Rii.Sliceable (Raw α β cmp) α (DTreeMap.Internal.Const.RiiSlice α β) where
  mkSlice carrier range := ⟨carrier.inner.inner, range⟩

@[simp] public theorem toList_rii {α : Type ąu} {β : Type v}
    (cmp : α → α → Ordering := by exact compare) {t : Raw α β cmp} :
    t[*...*].toList = t.toList := by
  apply DTreeMap.Internal.Const.toList_rii

public instance {α : Type u} {β : Type v} (cmp : α → α → Ordering := by exact compare) :
    Ric.Sliceable (Raw α β cmp) α (@DTreeMap.Internal.Const.RicSlice α β ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner.inner, range⟩⟩

public theorem toList_ric {α : Type u} {β : Type v} (cmp : α → α → Ordering := by exact compare)
    [TransCmp cmp] {t : Raw α β cmp} (wf : t.WF) {bound : α} :
    t[*...=bound].toList = t.toList.filter (fun e => (cmp e.fst bound).isLE) := by
  apply @DTreeMap.Internal.Const.toList_ric _ _ ⟨cmp⟩ _ _
  · exact @wf.out.out.ordered _ _ ⟨cmp⟩ _

public instance {α : Type u} {β : Type v} (cmp : α → α → Ordering := by exact compare) :
    Rio.Sliceable (Raw α β cmp) α (@DTreeMap.Internal.Const.RioSlice α β ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner.inner, range⟩⟩

public theorem toList_rio {α : Type u} {β : Type v} (cmp : α → α → Ordering := by exact compare)
    [TransCmp cmp] {t : Raw α β cmp} (wf : t.WF) {bound : α} :
    t[*...<bound].toList = t.toList.filter (fun e => (cmp e.fst bound).isLT) := by
  apply @DTreeMap.Internal.Const.toList_rio _ _ ⟨cmp⟩ _ _
  · exact @wf.out.out.ordered _ _ ⟨cmp⟩ _

public instance {α : Type u} {β : Type v} (cmp : α → α → Ordering := by exact compare) :
    Rci.Sliceable (Raw α β cmp) α (@DTreeMap.Internal.Const.RciSlice α β ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner.inner, range⟩⟩

public theorem toList_rci {α : Type u} {β : Type v} (cmp : α → α → Ordering := by exact compare)
    [TransCmp cmp] {t : Raw α β cmp} (wf : t.WF) {bound : α} :
    t[bound...*].toList = t.toList.filter (fun e => (cmp e.fst bound).isGE) := by
  apply @DTreeMap.Internal.Const.toList_rci _ _ ⟨cmp⟩ _ _
  · exact @wf.out.out.ordered _ _ ⟨cmp⟩ _

public instance {α : Type u} {β : Type v} (cmp : α → α → Ordering := by exact compare) :
    Rco.Sliceable (Raw α β cmp) α (@DTreeMap.Internal.Const.RcoSlice α β ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner.inner, range⟩⟩

public theorem toList_rco {α : Type u} {β : Type v} (cmp : α → α → Ordering := by exact compare)
    [TransCmp cmp] {t : Raw α β cmp} (wf : t.WF) {lowerBound upperBound : α} :
    t[lowerBound...<upperBound].toList =
      t.toList.filter (fun e => (cmp e.fst lowerBound).isGE ∧ (cmp e.fst upperBound).isLT) := by
  apply @DTreeMap.Internal.Const.toList_rco _ _ ⟨cmp⟩ _ _
  · exact @wf.out.out.ordered _ _ ⟨cmp⟩ _

public instance {α : Type u} {β : Type v} (cmp : α → α → Ordering := by exact compare) :
    Rcc.Sliceable (Raw α β cmp) α (@DTreeMap.Internal.Const.RccSlice α β ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner.inner, range⟩⟩

public theorem toList_rcc {α : Type u} {β : Type v} (cmp : α → α → Ordering := by exact compare)
    [TransCmp cmp] {t : Raw α β cmp} (wf : t.WF) {lowerBound upperBound : α} :
    t[lowerBound...=upperBound].toList =
      t.toList.filter (fun e => (cmp e.fst lowerBound).isGE ∧ (cmp e.fst upperBound).isLE) := by
  apply @DTreeMap.Internal.Const.toList_rcc _ _ ⟨cmp⟩ _ _
  · exact @wf.out.out.ordered _ _ ⟨cmp⟩ _

public instance {α : Type u} {β : Type v} (cmp : α → α → Ordering := by exact compare) :
    Roi.Sliceable (Raw α β cmp) α (@DTreeMap.Internal.Const.RoiSlice α β ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner.inner, range⟩⟩

public theorem toList_roi {α : Type u} {β : Type v} (cmp : α → α → Ordering := by exact compare)
    [TransCmp cmp] {t : Raw α β cmp} (wf : t.WF) {bound: α} : t[bound<...*].toList =
      t.toList.filter (fun e => (cmp e.fst bound).isGT) := by
  apply @DTreeMap.Internal.Const.toList_roi _ _ ⟨cmp⟩ _
  · exact @wf.out.out.ordered _ _ ⟨cmp⟩ _

public instance {α : Type u} {β : Type v} (cmp : α → α → Ordering := by exact compare) :
    Roc.Sliceable (Raw α β cmp) α (@DTreeMap.Internal.Const.RocSlice α β ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner.inner, range⟩⟩

public theorem toList_roc {α : Type u} {β : Type v} (cmp : α → α → Ordering := by exact compare)
    [TransCmp cmp] {t : Raw α β cmp} (wf : t.WF) {lowerBound upperBound : α} :
    t[lowerBound<...=upperBound].toList =
      t.toList.filter (fun e => (cmp e.fst lowerBound).isGT ∧ (cmp e.fst upperBound).isLE) := by
  apply @DTreeMap.Internal.Const.toList_roc _ _ ⟨cmp⟩ _
  · exact @wf.out.out.ordered _ _ ⟨cmp⟩ _

public instance {α : Type u} {β : Type v} (cmp : α → α → Ordering := by exact compare) :
    Roo.Sliceable (Raw α β cmp) α (@DTreeMap.Internal.Const.RooSlice α β ⟨cmp⟩) :=
  letI _ : Ord α := ⟨cmp⟩; ⟨fun carrier range => ⟨carrier.inner.inner, range⟩⟩

public theorem toList_roo {α : Type u} {β : Type v} (cmp : α → α → Ordering := by exact compare)
    [TransCmp cmp] {t : Raw α β cmp} (wf : t.WF) {lowerBound upperBound : α} :
    t[lowerBound<...upperBound].toList =
      t.toList.filter (fun e => (cmp e.fst lowerBound).isGT ∧ (cmp e.fst upperBound).isLT) := by
  apply @DTreeMap.Internal.Const.toList_roo _ _ ⟨cmp⟩ _
  · exact @wf.out.out.ordered _ _ ⟨cmp⟩ _

end Std.TreeMap.Raw
