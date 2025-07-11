/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Classes.Ord.Basic
import Std.Data.DTreeMap.Internal.Def
import Std.Data.Internal.Cut
import Std.Classes.Ord.New.LinearPreorder

/-!
# `Ordered` predicate

This file defines what it means for a tree map to be ordered. This definition is encoded in the
`Ordered` predicate.
-/

set_option autoImplicit false
set_option linter.all true

universe u v w

variable {α : Type u} {β : α → Type v}

namespace Std.DTreeMap.Internal.Impl
open Std.Internal

/-- Implementation detail of the tree map -/
def Ordered [LT α] (t : Impl α β) : Prop :=
  t.toListModel.Pairwise (fun a b => a.1 < b.1)

/-!
## Lemmas about the `Ordered` predicate
-/

theorem Ordered.left [LT α] {sz k v l r} (h : (.inner sz k v l r : Impl α β).Ordered) :
    l.Ordered :=
  h.sublist (by simp)

theorem Ordered.right [LT α] {sz k v l r} (h : (.inner sz k v l r : Impl α β).Ordered) :
    r.Ordered :=
  h.sublist (by simp)

theorem Ordered.gt_left [LT α] {sz k v l r} (h : (.inner sz k v l r : Impl α β).Ordered)
    {k'} (hk' : k' ∈ l.toListModel) : k'.1 < k :=
  h.rel_of_mem_append hk' List.mem_cons_self

theorem Ordered.compare_left_beq_gt [Ord α] [Comparable α] [LawfulOrd α] [LawfulLinearPreorder α]
    {k : α → Ordering} [IsStrictCut k]
    {sz k' v' l r} (ho : (.inner sz k' v' l r : Impl α β).Ordered) (hcmp : (k k').isGE)
    (p) (hp : p ∈ l.toListModel) : k p.1 == .gt :=
  beq_iff_eq.2 (IsStrictCut.gt_of_isGE_of_gt hcmp (ho.gt_left hp))

theorem Ordered.compare_left_not_beq_eq [Ord α] [Comparable α] [LawfulOrd α] [LawfulLinearPreorder α]
    {k : α → Ordering}
    [IsStrictCut k] {sz k' v' l r}
    (ho : (.inner sz k' v' l r : Impl α β).Ordered) (hcmp : (k k').isGE)
    (p) (hp : p ∈ l.toListModel) : ¬(k p.1 == .eq) := by
  suffices k p.fst = .gt by simp [this]
  exact IsStrictCut.gt_of_isGE_of_gt hcmp (ho.gt_left hp)

theorem Ordered.lt_right [LT α] {sz k v l r}
    (h : (.inner sz k v l r : Impl α β).Ordered) {k'} (hk' : k' ∈ r.toListModel) :
    k < k'.1 := by
  exact List.rel_of_pairwise_cons (h.sublist (List.sublist_append_right _ _)) hk'

theorem Ordered.compare_right_not_beq_gt [Ord α] [Comparable α] [LawfulOrd α] [LawfulComparable α]
    {k : α → Ordering} [IsStrictCut k] {sz k' v' l r}
    (ho : (.inner sz k' v' l r : Impl α β).Ordered) (hcmp : (k k').isLE)
    (p) (hp : p ∈ r.toListModel) : ¬(k p.1 == .gt) := by
  suffices k p.fst = .lt by simp [this]
  exact IsStrictCut.lt_of_isLE_of_lt hcmp (ho.lt_right hp)
