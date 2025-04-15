/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Classes.Ord
import Std.Data.DTreeMap.Internal.Def
import Std.Data.Internal.Cut

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
def Ordered [Ord α] (t : Impl α β) : Prop :=
  t.toListModel.Pairwise (fun a b => compare a.1 b.1 = .lt)

/-!
## Lemmas about the `Ordered` predicate
-/

theorem Ordered.left [Ord α] {sz k v l r} (h : (.inner sz k v l r : Impl α β).Ordered) :
    l.Ordered :=
  h.sublist (by simp)

theorem Ordered.right [Ord α] {sz k v l r} (h : (.inner sz k v l r : Impl α β).Ordered) :
    r.Ordered :=
  h.sublist (by simp)

theorem Ordered.compare_left [Ord α] {sz k v l r} (h : (.inner sz k v l r : Impl α β).Ordered)
    {k'} (hk' : k' ∈ l.toListModel) : compare k'.1 k = .lt :=
  h.rel_of_mem_append hk' List.mem_cons_self

theorem Ordered.compare_left_beq_gt [Ord α] [TransOrd α] {k : α → Ordering} [IsStrictCut compare k]
    {sz k' v' l r} (ho : (.inner sz k' v' l r : Impl α β).Ordered) (hcmp : (k k').isGE)
    (p) (hp : p ∈ l.toListModel) : k p.1 == .gt :=
 beq_iff_eq.2 (IsStrictCut.gt_of_isGE_of_gt hcmp (OrientedCmp.gt_of_lt (ho.compare_left hp)))

theorem Ordered.compare_left_not_beq_eq [Ord α] [TransOrd α] {k : α → Ordering}
    [IsStrictCut compare k] {sz k' v' l r}
    (ho : (.inner sz k' v' l r : Impl α β).Ordered) (hcmp : (k k').isGE)
    (p) (hp : p ∈ l.toListModel) : ¬(k p.1 == .eq) := by
  suffices k p.fst = .gt by simp [this, OrientedCmp.eq_comm (a := k)]
  exact IsStrictCut.gt_of_isGE_of_gt hcmp (OrientedCmp.gt_of_lt (ho.compare_left hp))

theorem Ordered.compare_right [Ord α] {sz k v l r}
    (h : (.inner sz k v l r : Impl α β).Ordered) {k'} (hk' : k' ∈ r.toListModel) :
    compare k k'.1 = .lt := by
  exact List.rel_of_pairwise_cons (h.sublist (List.sublist_append_right _ _)) hk'

theorem Ordered.compare_right_not_beq_gt [Ord α] [TransOrd α] {k : α → Ordering}
    [IsStrictCut compare k] {sz k' v' l r}
    (ho : (.inner sz k' v' l r : Impl α β).Ordered) (hcmp : (k k').isLE)
    (p) (hp : p ∈ r.toListModel) : ¬(k p.1 == .gt) := by
  suffices k p.fst = .lt by simp [this]
  exact IsStrictCut.lt_of_isLE_of_lt hcmp (ho.compare_right hp)
