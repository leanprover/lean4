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

public theorem Rii.correct {α : Type u} {β : α → Type v} [Ord α] {t : Raw α β compare} : t[*...*].toList = t.toList := by
  apply Internal.Rii.correct

public instance {α : Type u} {β : α → Type v} [Ord α] (cmp : α → α → Ordering := by exact compare) :
    Ric.Sliceable (Raw α β cmp) α (Internal.RicSlice α β) where
  mkSlice carrier range := ⟨carrier.inner, range⟩

public theorem Ric.correct {α : Type u} {β : α → Type v} [Ord α] [TransOrd α] {t : Raw α β compare} {wf : t.WF} {bound : α} :
  t[*...=bound].toList = t.toList.filter (fun e => (compare e.fst bound).isLE) := by
  apply Internal.Ric.correct
  . exact wf.out.ordered

public instance {α : Type u} {β : α → Type v} [Ord α] (cmp : α → α → Ordering := by exact compare) :
    Rio.Sliceable (Raw α β cmp) α (Internal.RioSlice α β) where
  mkSlice carrier range := ⟨carrier.inner, range⟩

public theorem Rio.correct {α : Type u} {β : α → Type v} [Ord α] [TransOrd α] {t : Raw α β compare} {wf : t.WF} {bound : α} :
  t[*...<bound].toList = t.toList.filter (fun e => (compare e.fst bound).isLT) := by
  apply Internal.Rio.correct
  . exact wf.out.ordered

public instance {α : Type u} {β : α → Type v} [Ord α] (cmp : α → α → Ordering := by exact compare) :
    Rci.Sliceable (Raw α β cmp) α (Internal.RciSlice α β) where
  mkSlice carrier range := ⟨carrier.inner, range⟩

public theorem Rci.correct {α : Type u} {β : α → Type v} [Ord α] [TransOrd α] {t : Raw α β compare} {wf : t.WF} {bound : α} :
  t[bound...*].toList = t.toList.filter (fun e => (compare e.fst bound).isGE) := by
  apply Internal.Rci.correct
  . exact wf.out.ordered

public instance {α : Type u} {β : α → Type v} [Ord α] (cmp : α → α → Ordering := by exact compare) :
    Rco.Sliceable (Raw α β cmp) α (Internal.RcoSlice α β) where
  mkSlice carrier range := ⟨carrier.inner, range⟩

public theorem Rco.correct {α : Type u} {β : α → Type v} [Ord α] [TransOrd α] {t : Raw α β compare} {wf : t.WF} {lower_bound upper_bound : α} :
  t[lower_bound...<upper_bound].toList = t.toList.filter (fun e => (compare e.fst lower_bound).isGE ∧ (compare e.fst upper_bound).isLT) := by
  apply Internal.Rco.correct
  . exact wf.out.ordered

public instance {α : Type u} {β : α → Type v} [Ord α] (cmp : α → α → Ordering := by exact compare) :
    Rcc.Sliceable (Raw α β cmp) α (Internal.RccSlice α β) where
  mkSlice carrier range := ⟨carrier.inner, range⟩

public theorem Rcc.correct {α : Type u} {β : α → Type v} [Ord α] [TransOrd α] {t : Raw α β compare} {wf : t.WF} {lower_bound upper_bound : α} :
  t[lower_bound...=upper_bound].toList =
    t.toList.filter (fun e => (compare e.fst lower_bound).isGE ∧ (compare e.fst upper_bound).isLE) := by
  apply Internal.Rcc.correct
  . exact wf.out.ordered

public instance {α : Type u} {β : α → Type v} [Ord α] (cmp : α → α → Ordering := by exact compare) :
    Roi.Sliceable (Raw α β cmp) α (Internal.RoiSlice α β) where
  mkSlice carrier range := ⟨carrier.inner, range⟩

public theorem Roi.correct {α : Type u} {β : α → Type v} [Ord α] [TransOrd α] {t : Raw α β compare} {wf : t.WF} {bound: α} :
  t[bound<...*].toList =
    t.toList.filter (fun e => (compare e.fst bound).isGT) := by
  apply Internal.Roi.correct
  . exact wf.out.ordered

public instance {α : Type u} {β : α → Type v} [Ord α] (cmp : α → α → Ordering := by exact compare) :
    Roc.Sliceable (Raw α β cmp) α (Internal.RocSlice α β) where
  mkSlice carrier range := ⟨carrier.inner, range⟩

public theorem Roc.correct {α : Type u} {β : α → Type v} [Ord α] [TransOrd α] {t : Raw α β compare} {wf : t.WF} {lower_bound upper_bound : α} :
  t[lower_bound<...=upper_bound].toList =
    t.toList.filter (fun e => (compare e.fst lower_bound).isGT ∧ (compare e.fst upper_bound).isLE) := by
  apply Internal.Roc.correct
  . exact wf.out.ordered

public instance {α : Type u} {β : α → Type v} [Ord α] (cmp : α → α → Ordering := by exact compare) :
    Roo.Sliceable (Raw α β cmp) α (Internal.RooSlice α β) where
  mkSlice carrier range := ⟨carrier.inner, range⟩

public theorem Roo.correct {α : Type u} {β : α → Type v} [Ord α] [TransOrd α] {t : Raw α β compare} {wf : t.WF} {lower_bound upper_bound : α} :
  t[lower_bound<...upper_bound].toList =
    t.toList.filter (fun e => (compare e.fst lower_bound).isGT ∧ (compare e.fst upper_bound).isLT) := by
  apply Internal.Roo.correct
  . exact wf.out.ordered

end Std.DTreeMap.Raw
