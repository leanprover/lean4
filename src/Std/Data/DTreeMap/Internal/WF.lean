/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Orderedtree.DTreeMap.Internal.Model
import Orderedtree.Classes.TransOrd
import Orderedtree.Classes.Cut
import Orderedtree.DTreeMap.Internal.List.Associative
import Std.Data.DHashMap.Internal.List.Associative

/-!
# Low-level proofs about size-bounded trees
-/

set_option autoImplicit false
set_option linter.all true

universe u v w

variable {α : Type u} {β : α → Type v} {γ : α → Type w} {δ : Type w}

namespace Std.DTreeMap.Internal.Impl

@[simp] theorem toListModel_leaf : (.leaf : Impl α β).toListModel = [] := rfl
@[simp] theorem toListModel_inner {sz k v l r} :
  (.inner sz k v l r : Impl α β).toListModel = l.toListModel ++ ⟨k, v⟩ :: r.toListModel := rfl

/-!
## `toListModel` for balancing operations
-/

@[simp]
theorem toListModel_balance {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    (balance k v l r hlb hrb hlr).toListModel = l.toListModel ++ ⟨k, v⟩ :: r.toListModel := by
  rw [balance.eq_def]
  repeat' (split; try dsimp only)
  all_goals
    try contradiction
    try simp; done
  all_goals
    rename_i l r _ _ _
    cases l <;> cases r <;> (try simp; done) <;> (exfalso; tree_tac)

@[simp]
theorem toListModel_balanceL {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    (balanceL k v l r hlb hrb hlr).toListModel = l.toListModel ++ ⟨k, v⟩ :: r.toListModel := by
  rw [balanceL_eq_balance, toListModel_balance]

@[simp]
theorem toListModel_balanceLErase {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    (balanceLErase k v l r hlb hrb hlr).toListModel = l.toListModel ++ ⟨k, v⟩ :: r.toListModel := by
  rw [balanceLErase_eq_balance, toListModel_balance]

@[simp]
theorem toListModel_balanceR {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    (balanceR k v l r hlb hrb hlr).toListModel = l.toListModel ++ ⟨k, v⟩ :: r.toListModel := by
  rw [balanceR_eq_balance, toListModel_balance]

@[simp]
theorem toListModel_balanceRErase {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    (balanceRErase k v l r hlb hrb hlr).toListModel = l.toListModel ++ ⟨k, v⟩ :: r.toListModel := by
  rw [balanceRErase_eq_balance, toListModel_balance]

@[simp]
theorem toListModel_minView {k : α} {v : β k} {l r : Impl α β} {hl hr hlr} :
    ⟨(minView k v l r hl hr hlr).k, (minView k v l r hl hr hlr).v⟩ ::
      (minView k v l r hl hr hlr).tree.impl.toListModel =
    l.toListModel ++ ⟨k, v⟩ :: r.toListModel := by
  induction k, v, l, r, hl, hr, hlr using minView.induct
  · simp [minView]
  · rename_i ih
    simp [minView, ← ih]

@[simp]
theorem toListModel_maxView {k : α} {v : β k} {l r : Impl α β} {hl hr hlr} :
    (maxView k v l r hl hr hlr).tree.impl.toListModel ++
      [⟨(maxView k v l r hl hr hlr).k, (maxView k v l r hl hr hlr).v⟩] =
    l.toListModel ++ ⟨k, v⟩ :: r.toListModel := by
  induction k, v, l, r, hl, hr, hlr using maxView.induct <;> simp_all [maxView]

@[simp]
theorem toListModel_glue {l r : Impl α β} {hl hr hlr} :
    (glue l r hl hr hlr).toListModel = l.toListModel ++ r.toListModel := by
  cases l <;> cases r
  all_goals try (simp [glue]; done)
  dsimp only [glue]
  split <;> try (simp; done)
  rw [toListModel_balanceRErase, ← List.singleton_append, ← List.append_assoc]
  simp

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
  h.rel_of_mem_append hk' (List.mem_cons_self _ _)

theorem Ordered.compare_left_beq_gt [Ord α] [TransOrd α] {k : α → Ordering} [IsStrictCut compare k] {sz k' v' l r}
    (ho : (.inner sz k' v' l r : Impl α β).Ordered) (hcmp : (k k').isGE)
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

/-!
## Verification of model functions
-/

theorem toListModel_filter_gt_of_gt [Ord α] [TransOrd α] {k : α → Ordering} [IsStrictCut compare k]
    {sz k' v' l r} (hcmp : k k' = .gt) (ho : (inner sz k' v' l r).Ordered) :
    (inner sz k' v' l r : Impl α β).toListModel.filter (k ·.1 == .gt) =
      l.toListModel ++ ⟨k', v'⟩ :: r.toListModel.filter (k ·.1 == .gt) := by
  rw [toListModel_inner, List.filter_append, List.filter_cons_of_pos, List.filter_eq_self.2]
  · exact Ordered.compare_left_beq_gt ho (Ordering.isGE_of_eq_gt hcmp)
  · simpa

theorem toListModel_filter_gt_of_eq [Ord α] [TransOrd α] {k : α → Ordering} [IsStrictCut compare k]
    {sz k' v' l r} (hcmp : k k' = .eq) (ho : (inner sz k' v' l r).Ordered) :
    (inner sz k' v' l r : Impl α β).toListModel.filter (k ·.1 == .gt) = l.toListModel := by
  rw [toListModel_inner, List.filter_append, List.filter_cons_of_neg, List.filter_eq_self.2,
    List.filter_eq_nil_iff.2, List.append_nil]
  · exact Ordered.compare_right_not_beq_gt ho (Ordering.isLE_of_eq_eq hcmp)
  · exact Ordered.compare_left_beq_gt ho (Ordering.isGE_of_eq_eq hcmp)
  · simp_all

theorem toListModel_filter_gt_of_lt [Ord α] [TransOrd α] {k : α → Ordering} [IsStrictCut compare k] {sz k' v' l r}
    (hcmp : k k' = .lt) (ho : (inner sz k' v' l r).Ordered) :
    (inner sz k' v' l r : Impl α β).toListModel.filter (k ·.1 == .gt) =
      l.toListModel.filter (k ·.1 == .gt) := by
  rw [toListModel_inner, List.filter_append, (List.filter_eq_nil_iff (l := _ :: _)).2,
    List.append_nil]
  simpa [hcmp] using Ordered.compare_right_not_beq_gt ho (Ordering.isLE_of_eq_lt hcmp)

theorem toListModel_find?_of_gt [Ord α] [TransOrd α] {k : α → Ordering} [IsStrictCut compare k] {sz k' v' l r}
    (hcmp : k k' = .gt) (ho : (inner sz k' v' l r).Ordered) :
    (inner sz k' v' l r : Impl α β).toListModel.find? (k ·.1 == .eq) =
      r.toListModel.find? (k ·.1 == .eq) := by
  rw [toListModel_inner, List.find?_append, List.find?_eq_none.2, Option.none_or,
    List.find?_cons_of_neg]
  · simp [hcmp]
  · exact Ordered.compare_left_not_beq_eq ho (Ordering.isGE_of_eq_gt hcmp)

theorem toListModel_find?_of_eq [Ord α] [TransOrd α] {k : α → Ordering} [IsStrictCut compare k] {sz k' v' l r}
    (hcmp : k k' = .eq) (ho : (inner sz k' v' l r).Ordered) :
    (inner sz k' v' l r : Impl α β).toListModel.find? (k ·.1 == .eq) = some ⟨k', v'⟩ := by
  rw [toListModel_inner, List.find?_append, List.find?_eq_none.2, Option.none_or,
    List.find?_cons_of_pos]
  · simp_all
  · exact Ordered.compare_left_not_beq_eq ho (Ordering.isGE_of_eq_eq hcmp)

theorem Option.or_eq_left {o o' : Option α} (h : o' = none) : o.or o' = o := by
  cases h; simp

theorem toListModel_find?_of_lt [Ord α] [TransOrd α] {k : α → Ordering} [IsCut compare k]
    {sz k' v' l r} (hcmp : k k' = .lt) (ho : (inner sz k' v' l r).Ordered) :
    (inner sz k' v' l r : Impl α β).toListModel.find? (k ·.1 == .eq) =
      l.toListModel.find? (k ·.1 == .eq) := by
  rw [toListModel_inner, List.find?_append, Option.or_eq_left]
  rw [List.find?_cons_of_neg _ (by simp [hcmp])]
  refine List.find?_eq_none.2 (fun p hp => by simp [IsCut.lt hcmp (ho.compare_right hp)])

theorem toListModel_filter_lt_of_gt [Ord α] [TransOrd α] {k : α → Ordering} [IsCut compare k] {sz k' v' l r}
    (hcmp : k k' = .gt) (ho : (inner sz k' v' l r).Ordered) :
    (inner sz k' v' l r : Impl α β).toListModel.filter (k ·.1 == .lt) =
      r.toListModel.filter (k ·.1 == .lt) := by
  rw [toListModel_inner, List.filter_append, List.filter_eq_nil_iff.2, List.nil_append,
    List.filter_cons_of_neg (by simp [hcmp])]
  exact fun p hp => by simp [IsCut.gt hcmp (OrientedCmp.gt_of_lt (ho.compare_left hp))]

theorem toListModel_filter_lt_of_eq [Ord α] [TransOrd α] {k : α → Ordering} [IsStrictCut compare k] {sz k' v' l r}
    (hcmp : k k' = .eq) (ho : (inner sz k' v' l r).Ordered) :
    (inner sz k' v' l r : Impl α β).toListModel.filter (k ·.1 == .lt) = r.toListModel := by
  rw [toListModel_inner, List.filter_append, List.filter_eq_nil_iff.2, List.nil_append,
    List.filter_cons_of_neg (by simp [hcmp]), List.filter_eq_self]
  · exact fun p hp => by simp [IsStrictCut.lt_of_isLE_of_lt (Ordering.isLE_of_eq_eq hcmp) (ho.compare_right hp)]
  · exact fun p hp => by simp [IsStrictCut.gt_of_isGE_of_gt (Ordering.isGE_of_eq_eq hcmp) (OrientedCmp.gt_of_lt (ho.compare_left hp))]

theorem toListModel_filter_lt_of_lt [Ord α] [TransOrd α] {k : α → Ordering} [IsCut compare k] {sz k' v' l r}
    (hcmp : k k' = .lt) (ho : (inner sz k' v' l r).Ordered) :
    (inner sz k' v' l r : Impl α β).toListModel.filter (k ·.1 == .lt) =
      l.toListModel.filter (k ·.1 == .lt) ++ ⟨k', v'⟩ :: r.toListModel := by
  simp only [toListModel_inner, List.filter_append, hcmp, beq_self_eq_true, List.filter_cons_of_pos,
    List.append_cancel_left_eq, List.cons.injEq, List.filter_eq_self, beq_iff_eq, true_and]
  exact fun p hp => IsCut.lt hcmp (ho.compare_right hp)

instance [Ord α] [TransOrd α] {k : α} : IsStrictCut compare (compare k) where
  lt := TransCmp.lt_trans
  gt h₁ h₂ := OrientedCmp.gt_of_lt (TransCmp.lt_trans (OrientedCmp.lt_of_gt h₂)
    (OrientedCmp.lt_of_gt h₁))
  eq _ _ := TransCmp.congr_left

theorem findCell_of_gt [Ord α] [TransOrd α] {k : α → Ordering} [IsStrictCut compare k] {sz k' v' l r}
    (hcmp : k k' = .gt) (ho : (inner sz k' v' l r : Impl α β).Ordered) :
    List.findCell (inner sz k' v' l r).toListModel k = List.findCell r.toListModel k :=
  Cell.ext (toListModel_find?_of_gt hcmp ho)

theorem findCell_of_eq [Ord α] [TransOrd α] {k : α → Ordering} [IsStrictCut compare k] {sz k' v' l r}
    (hcmp : k k' = .eq) (ho : (inner sz k' v' l r : Impl α β).Ordered) :
    List.findCell (inner sz k' v' l r).toListModel k = Cell.ofEq k' v' hcmp :=
  Cell.ext (toListModel_find?_of_eq hcmp ho)

theorem findCell_of_lt [Ord α] [TransOrd α] {k : α → Ordering} [IsCut compare k] {sz k' v' l r}
    (hcmp : k k' = .lt) (ho : (inner sz k' v' l r : Impl α β).Ordered) :
    List.findCell (inner sz k' v' l r).toListModel k = List.findCell l.toListModel k :=
  Cell.ext (toListModel_find?_of_lt hcmp ho)

theorem toListModel_updateCell [Ord α] [TransOrd α] {k : α}
    {f : Cell α β (compare k) → Cell α β (compare k)} {l : Impl α β} (hlb : l.Balanced)
    (hlo : l.Ordered) :
    (l.updateCell k f hlb).impl.toListModel = l.toListModel.filter (compare k ·.1 == .gt) ++
      (f (List.findCell l.toListModel (compare k))).inner.toList ++
      l.toListModel.filter (compare k ·.1 == .lt) := by
  induction l, hlb using updateCell.induct k f
  · simp_all [updateCell]
  · simp_all [updateCell]
  · rename_i sz k' v' l r hb hcmp l' hl'₁ hl'₂ hl'₃ hup hb' ih
    simp only [updateCell, hcmp]
    split <;> rename_i hcmp' <;> try (simp [hcmp] at hcmp'; done)
    rw [toListModel_balance, toListModel_filter_gt_of_lt hcmp hlo,
      toListModel_filter_lt_of_lt hcmp hlo, findCell_of_lt hcmp hlo, ih hlo.left]
    simp
  · rename_i sz k' v' l r hl hcmp hf hl'
    simp only [updateCell, hcmp, hf]
    split <;> rename_i hcmp' <;> try (simp [hcmp] at hcmp'; done)
    rw [toListModel_glue, toListModel_filter_gt_of_eq hcmp hlo, findCell_of_eq hcmp hlo,
      hf, toListModel_filter_lt_of_eq hcmp hlo]
    simp
  · rename_i sz k' v' l r hl hcmp k'' v'' hf hl'
    simp only [updateCell, hcmp, hf]
    split <;> rename_i hcmp' <;> try (simp [hcmp] at hcmp'; done)
    rw [toListModel_inner, toListModel_filter_gt_of_eq hcmp hlo, findCell_of_eq hcmp hlo,
      toListModel_filter_lt_of_eq hcmp hlo, hf]
    simp
  · rename_i sz k' v' l r hb hcmp l' hl'₁ hl'₂ hl'₃ hup hb' ih
    simp only [updateCell, hcmp]
    split <;> rename_i hcmp' <;> try (simp [hcmp] at hcmp'; done)
    rw [toListModel_filter_gt_of_gt hcmp hlo, findCell_of_gt hcmp hlo,
      toListModel_filter_lt_of_gt hcmp hlo, toListModel_balance, ih hlo.right]
    simp

theorem toListModel_eq_append [Ord α] [TransOrd α] (k : α → Ordering) [IsStrictCut compare k] {l : Impl α β} (ho : l.Ordered) :
    l.toListModel = l.toListModel.filter (k ·.1 == .gt) ++
      (l.toListModel.find? (k ·.1 == .eq)).toList ++
      l.toListModel.filter (k ·.1 == .lt) := by
  induction l
  · rename_i sz k' v l r ih₁ ih₂
    cases hcmp : k k'
    · rw [toListModel_filter_gt_of_lt hcmp ho, toListModel_find?_of_lt hcmp ho,
        toListModel_filter_lt_of_lt hcmp ho, toListModel_inner]
      conv => lhs; rw [ih₁ ho.left]
      simp
    · rw [toListModel_filter_gt_of_eq hcmp ho, toListModel_find?_of_eq hcmp ho,
        toListModel_filter_lt_of_eq hcmp ho, toListModel_inner]
      simp
    · rw [toListModel_filter_gt_of_gt hcmp ho, toListModel_find?_of_gt hcmp ho,
        toListModel_filter_lt_of_gt hcmp ho, toListModel_inner]
      conv => lhs; rw [ih₂ ho.right]
      simp
  · simp

theorem Option.pairwise_toList {P : α → α → Prop} {o : Option α} : o.toList.Pairwise P := by
  cases o <;> simp

theorem ordered_updateAtKey [Ord α] [TransOrd α] {k : α}
    {f : Cell α β (compare k) → Cell α β (compare k)}
    {l : Impl α β} (hlb : l.Balanced) (hlo : l.Ordered) : (l.updateCell k f hlb).impl.Ordered := by
  rw [Ordered, toListModel_updateCell _ hlo]
  rw [Ordered, toListModel_eq_append (compare k) hlo] at hlo
  simp only [List.pairwise_append] at hlo ⊢
  refine ⟨⟨hlo.1.1, Option.pairwise_toList, ?_⟩, ⟨hlo.2.1, ?_⟩⟩
  · intro a ha b hb
    have := hlo.2.2 a (List.mem_append_left _ ha)
    clear hlo
    simp at ha hb
    have : compare k b.fst = .eq := (f (List.findCell l.toListModel (compare k))).property _ hb
    exact TransCmp.lt_of_lt_of_eq (OrientedCmp.lt_of_gt ha.2) this
  · intro a ha b hb
    rw [List.mem_append] at ha
    obtain ha|ha := ha
    · exact hlo.2.2 a (List.mem_append_left _ ha) _ hb
    · simp at ha
      have h₀ : compare k a.fst = .eq := (f (List.findCell l.toListModel (compare k))).property _ ha
      have h₁ : compare k b.fst = .lt := by
        simp only [List.mem_filter, beq_iff_eq] at hb
        exact hb.2
      exact TransCmp.lt_of_eq_of_lt (OrientedCmp.eq_symm h₀) h₁

/-!
## Connecting the tree maps machinery to the hash map machinery
-/

/-- Internal function to derive a `BEq` instance from an `Ord` instance in order to connect the
verification machinery for tree maps to the verification machinery for hash maps. -/
def beqOfOrd [Ord α] : BEq α where
  beq a b := compare a b == .eq

attribute [local instance] beqOfOrd

@[local simp]
theorem beq_eq [Ord α] {a b : α} : (a == b) = (compare a b == .eq) :=
  rfl

@[local instance]
theorem equivBEq_of_transOrd [Ord α] [TransOrd α] : EquivBEq α where
  symm {a b} h := by simp_all [OrientedCmp.eq_comm]
  trans h₁ h₂ := by simp_all only [beq_eq, beq_iff_eq]; exact TransCmp.eq_trans h₁ h₂
  refl := by simp

open Std.DHashMap.Internal.List

theorem exists_cell_of_updateAtKey [Ord α] [TransOrd α] (l : Impl α β) (hlb : l.Balanced)
    (hlo : l.Ordered) (k : α)
    (f : Cell α β (compare k) → Cell α β (compare k)) : ∃ (l' : List ((a : α) × β a)),
    l.toListModel.Perm ((l.toListModel.find? (compare k ·.1 == .eq)).toList ++ l') ∧
    (l.updateCell k f hlb).impl.toListModel.Perm
      ((f (List.findCell l.toListModel (compare k))).inner.toList ++ l') ∧
    (containsKey k l' = false) := by
  refine ⟨l.toListModel.filter (compare k ·.1 == .gt) ++
    l.toListModel.filter (compare k ·.1 == .lt), ?_, ?_, ?_⟩
  · conv => lhs; rw [toListModel_eq_append (compare k) hlo]
    simpa using List.perm_append_comm_assoc _ _ _
  · conv => lhs; rw [toListModel_updateCell hlb hlo]
    simpa using List.perm_append_comm_assoc _ _ _
  · rw [containsKey_eq_false_iff_forall_mem_keys, keys_eq_map]
    simp only [List.map_append, List.mem_append, List.mem_map, List.mem_filter, beq_iff_eq, beq_eq,
      beq_eq_false_iff_ne, ne_eq]
    rintro a (⟨p, ⟨⟨-, hp⟩, rfl⟩⟩|⟨p, ⟨⟨-, hp⟩, rfl⟩⟩) <;> simp_all

theorem Ordered.distinctKeys [Ord α] {l : Impl α β} (h : l.Ordered) :
    DistinctKeys l.toListModel :=
  ⟨by rw [keys_eq_map, List.pairwise_map]; exact h.imp (fun h => by simp_all)⟩

/-- This is the general theorem to show that modification operations are correct. -/
theorem toListModel_updateAtKey_perm [Ord α] [TransOrd α]
    {l : Impl α β} (hlb : l.Balanced) (hlo : l.Ordered) {k : α}
    {f : Cell α β (compare k) → Cell α β (compare k)}
    {g : List ((a : α) × β a) → List ((a : α) × β a)}
    (hfg : ∀ {c}, (f c).inner.toList = g c.inner.toList)
    (hg₁ : ∀ {l l'}, DistinctKeys l → List.Perm l l' → List.Perm (g l) (g l'))
    (hg₂ : ∀ {l l'}, containsKey k l' = false → g (l ++ l') = g l ++ l') :
    List.Perm (l.updateCell k f hlb).impl.toListModel (g l.toListModel) := by
  obtain ⟨l, h₁, h₂, h₃⟩ := exists_cell_of_updateAtKey l hlb hlo k f
  refine h₂.trans (List.Perm.trans ?_ (hg₁ hlo.distinctKeys h₁).symm)
  rwa [hfg, hg₂, List.findCell_inner]

theorem contains_findCell [Ord α] [TransOrd α] {k : α → Ordering} [IsStrictCut compare k] {l : Impl α β} (hlo : l.Ordered) (h : l.contains' k) :
    (List.findCell l.toListModel k).contains := by
  induction l
  · rename_i sz k' v' l r ih₁ ih₂
    cases hcmp : k k' <;> simp [contains', hcmp] at h
    · simpa only [findCell_of_lt hcmp hlo] using ih₁ hlo.left h
    · simp only [findCell_of_eq hcmp hlo, Cell.contains_ofEq]
    · simpa only [findCell_of_gt hcmp hlo] using ih₂ hlo.right h
  · simp [contains'] at h

theorem applyPartition_eq [Ord α] [TransOrd α] {k : α → Ordering} [IsStrictCut compare k] {l : Impl α β}
    {f : List ((a : α) × β a) → (c : Cell α β k) → (l.contains' k → c.contains) → List ((a : α ) × β a) → δ}
    (hlo : l.Ordered) :
    applyPartition k l f =
    f (l.toListModel.filter (k ·.1 == .gt)) (List.findCell l.toListModel k)
      (contains_findCell hlo) (l.toListModel.filter (k ·.1 == .lt)) := by
  rw [applyPartition]
  suffices ∀ ℓ ll rr h, ℓ.Ordered → (∀ p ∈ ll, k p.1 = .gt) → (∀ p ∈ rr, k p.1 = .lt) →
    (l.toListModel = ll ++ ℓ.toListModel ++ rr) →
      applyPartition.go k l f ll ℓ h rr = f (l.toListModel.filter (k ·.1 == .gt)) (List.findCell l.toListModel k) (contains_findCell hlo)
        (l.toListModel.filter (k ·.1 == .lt)) by simpa using this l [] [] id hlo
  intro ℓ ll rr h hℓo hll hrr hl
  induction ℓ generalizing ll rr
  · rename_i sz k' v' l' r' ih₁ ih₂
    simp only [applyPartition.go, List.cons_append, List.append_assoc]
    split <;> rename_i hcmp
    · rw [ih₁ _ _ _ hℓo.left]
      · exact hll
      · simp only [List.mem_cons, List.mem_append, forall_eq_or_imp, hcmp, true_and]
        rintro p (hp|hp)
        · exact IsCut.lt hcmp (hℓo.compare_right hp)
        · exact hrr _ hp
      · simp [hl]
    · congr
      · rw [hl, List.filter_append, List.filter_append, List.filter_eq_self.2,
        toListModel_filter_gt_of_eq hcmp hℓo, List.filter_eq_nil_iff.2, List.append_nil]
        · exact fun p hp => by simp [hrr p hp]
        · exact fun p hp => by simp [hll p hp]
      · apply Cell.ext
        rw [Cell.ofEq_inner, List.findCell_inner, hl, List.find?_append, List.find?_append,
          List.find?_eq_none.2, Option.none_or, toListModel_find?_of_eq hcmp hℓo, Option.some_or]
        exact fun p hp => by simp [hll p hp]
      · rw [hl, List.filter_append, List.filter_append, List.filter_eq_nil_iff.2, List.nil_append,
          toListModel_filter_lt_of_eq hcmp hℓo, List.filter_eq_self.2]
        · exact fun p hp => by simp [hrr p hp]
        · exact fun p hp => by simp [hll p hp]
    · rw [ih₂ _ _ _ hℓo.right]
      · simp only [List.mem_append, List.mem_singleton]
        rintro p (hp|hp|rfl)
        · exact hll _ hp
        · exact IsCut.gt hcmp (OrientedCmp.gt_of_lt (hℓo.compare_left hp))
        · exact hcmp
      · exact hrr
      · simp [hl]
  · simp only [applyPartition.go]
    congr
    · rw [hl, toListModel_leaf, List.append_nil, List.filter_append, List.filter_eq_self.2,
        List.filter_eq_nil_iff.2, List.append_nil]
      · exact fun p hp => by simp [hrr p hp]
      · exact fun p hp => by simp [hll p hp]
    · apply Cell.ext
      rw [Cell.empty_inner, List.findCell_inner, hl, toListModel_leaf, List.append_nil,
        List.find?_eq_none.2]
      simp only [List.mem_append, beq_iff_eq]
      rintro p (hp|hp)
      · simp [hll p hp]
      · simp [hrr p hp]
    · rw [hl, toListModel_leaf, List.append_nil, List.filter_append, List.filter_eq_nil_iff.2,
        List.filter_eq_self.2, List.nil_append]
      · exact fun p hp => by simp [hrr p hp]
      · exact fun p hp => by simp [hll p hp]

theorem containsKey_toListModel [Ord α] [OrientedOrd α] {k : α} {l : Impl α β} (h : l.contains' (compare k)) :
    containsKey k l.toListModel := by
  simp [containsKey_eq_true_iff_exists_mem]
  induction l
  · rename_i sz k' v' l r ih₁ ih₂
    simp only [toListModel_inner, containsKey_append, containsKey_cons, beq_eq, Bool.or_eq_true,
      beq_iff_eq]
    rw [contains'] at h
    split at h <;> rename_i hcmp
    · obtain ⟨p, hp₁, hp₂⟩ := ih₁ h
      exact ⟨p, by simp [hp₁], hp₂⟩
    · obtain ⟨p, hp₁, hp₂⟩ := ih₂ h
      exact ⟨p, by simp [hp₁], hp₂⟩
    · exact ⟨⟨k', v'⟩, by simp, OrientedCmp.eq_symm hcmp⟩
  · simp [contains'] at h

theorem Cell.containsKey_inner_toList [Ord α] [OrientedOrd α] {k : α} {c : Cell α β (compare k)} :
    c.contains → containsKey k c.inner.toList := by
  obtain ⟨(_|p), hp⟩ := c
  · simp [Cell.contains]
  · simp only [Cell.contains, Option.isSome_some, Option.toList_some, forall_const]
    exact containsKey_cons_of_beq (by simpa using (OrientedCmp.eq_symm (hp p rfl)))

theorem applyPartition_eq_apply_toListModel [Ord α] [TransOrd α] {k : α} {l : Impl α β} (hlo : l.Ordered)
    {f : List ((a : α) × β a) → (c : Cell α β (compare k)) → (l.contains' (compare k) → c.contains) → List ((a : α) × β a) → δ}
    (g : (ll : List ((a : α) × β a)) → (l.contains' (compare k) → containsKey k ll) → δ)
    (h : ∀ {ll rr : List ((a : α) × β a)} {c : Cell α β (compare k)} {h₁},
      (ll ++ c.inner.toList ++ rr).Pairwise (fun a b => compare a.1 b.1 = .lt) → (∀ p ∈ ll, compare k p.1 = .gt) →
      (∀ p ∈ rr, compare k p.1 = .lt) → f ll c h₁ rr = g (ll ++ c.inner.toList ++ rr)
      (fun p => by simp [Cell.containsKey_inner_toList (h₁ p)])) :
    applyPartition (compare k) l f = g l.toListModel containsKey_toListModel := by
  rw [applyPartition_eq hlo, h]
  · congr; exact (toListModel_eq_append _ hlo).symm
  · rw [List.findCell_inner, ← toListModel_eq_append _ hlo]
    exact hlo
  · simp
  · simp

theorem applyPartition_eq_apply_toListModel' [Ord α] [TransOrd α] {k : α → Ordering} [IsStrictCut compare k] {l : Impl α β} (hlo : l.Ordered)
    {f : List ((a : α) × β a) → (c : Cell α β k) → (l.contains' k → c.contains) → List ((a : α) × β a) → δ}
    (g : (ll : List ((a : α) × β a)) → δ)
    (h : ∀ {ll rr : List ((a : α) × β a)} {c : Cell α β k} {h₁},
      (ll ++ c.inner.toList ++ rr).Pairwise (fun a b => compare a.1 b.1 = .lt) → (∀ p ∈ ll, k p.1 = .gt) →
      (∀ p ∈ rr, k p.1 = .lt) → f ll c h₁ rr = g (ll ++ c.inner.toList ++ rr)) :
    applyPartition k l f = g l.toListModel := by
  rw [applyPartition_eq hlo, h]
  · congr; exact (toListModel_eq_append _ hlo).symm
  · rw [List.findCell_inner, ← toListModel_eq_append _ hlo]
    exact hlo
  · simp
  · simp

theorem applyCell_eq_apply_toListModel [Ord α] [TransOrd α] {k : α} {l : Impl α β} (hlo : l.Ordered)
    {f : (c : Cell α β (compare k)) → (l.contains' (compare k) → c.contains) → δ}
    (g : (ll : List ((a : α) × β a)) → (l.contains' (compare k) → containsKey k ll) → δ)
    (hfg : ∀ c hc, f c hc = g c.inner.toList (Cell.containsKey_inner_toList ∘ hc))
    (hg₁ : ∀ l₁ l₂ h, DistinctKeys l₁ → (hP : List.Perm l₁ l₂) → g l₁ h = g l₂ (containsKey_of_perm hP ▸ h))
    (hg : ∀ l₁ l₂ h, (h' : containsKey k l₂ = false) → g (l₁ ++ l₂) h = g l₁ (by simpa [h'] using h))
    : applyCell k l f = g l.toListModel containsKey_toListModel := by
  rw [applyCell_eq_applyPartition, applyPartition_eq_apply_toListModel hlo]
  intro ll rr c h₁ hd hll hrr
  have hperm : List.Perm (ll ++ c.inner.toList ++ rr) (c.inner.toList ++ (ll ++ rr)) := by
    simp only [List.append_assoc]; exact List.perm_append_comm_assoc ll c.inner.toList rr
  rw [hfg, hg₁ _ _ _ _ hperm, hg]
  · simp only [containsKey_append, Bool.or_eq_false_iff, containsKey_eq_false_iff_forall_mem_keys,
      keys_eq_map, List.mem_map, beq_eq, beq_eq_false_iff_ne, ne_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    exact ⟨fun p hp => by simp [hll p hp], fun p hp => by simp [hrr p hp]⟩
  · refine ⟨?_⟩
    rw [keys_eq_map, List.pairwise_map]
    exact hd.imp (fun hp => by simp_all)

/-!
## Verification of access operations
-/

@[simp]
theorem Option.head?_toList {o : Option α} : o.toList.head? = o := by
  cases o <;> simp

/-!
### `isEmpty`
-/

theorem isEmpty_eq_isEmpty (m : Impl α β) : m.isEmpty = m.toListModel.isEmpty := by
  induction m <;> simp [Impl.isEmpty]

/-!
### `lowerBound`
-/

theorem apply_lookupGEₘ [Ord α] [TransOrd α] {k : α} {l : Impl α β} (hlo : l.Ordered) :
    l.lookupGEₘ k = Std.DHashMap.Internal.List.lookupGE k l.toListModel := by
  rw [lookupGEₘ,
    applyPartition_eq_apply_toListModel hlo (fun l _ => Std.DHashMap.Internal.List.lookupGE k l)]
  intro ll rr c hc hp hll hrr
  rw [List.append_assoc, lookupGE_append_of_forall_mem_left hll,
    lookupGE_eq_head? _ (hp.sublist (by simp)), List.head?_append, Option.head?_toList]
  simp only [List.mem_append, Option.mem_toList, Option.mem_def]
  rintro p (hp|hp)
  · exact Ordering.isLE_of_eq_eq (c.property _ hp)
  · exact Ordering.isLE_of_eq_lt (hrr _ hp)

theorem apply_lookupGE [Ord α] [TransOrd α] {k : α} {l : Impl α β} (hlo : l.Ordered) :
    l.lookupGE k = Std.DHashMap.Internal.List.lookupGE k l.toListModel := by
  rw [lookupGE_eq_lookupGEₘ, apply_lookupGEₘ hlo]

/-!
### `min?`
-/

instance [Ord α] : IsStrictCut (compare : α → α → Ordering) (fun _ => .lt) where
  lt := by simp
  gt := by simp
  eq := by simp

theorem apply_min?ₘ [Ord α] [TransOrd α] {l : Impl α β} (hlo : l.Ordered) :
    l.min?ₘ = Std.DHashMap.Internal.List.min?' l.toListModel := by
  rw [min?ₘ, applyPartition_eq_apply_toListModel' hlo]
  simp only [List.append_assoc, reduceCtorEq, imp_false, implies_true, forall_const]
  intro ll rr c h₁ h₂ h₃
  obtain rfl : ll = [] := List.eq_nil_iff_forall_not_mem.2 h₃
  obtain hc : c.inner.toList = [] := by
    cases h : c.inner
    · simp
    · simpa [h] using c.property
  rw [hc, List.nil_append, List.nil_append, min?'_eq_head? (by simpa [hc] using h₂)]

theorem apply_min? [Ord α] [TransOrd α] {l : Impl α β} (hlo : l.Ordered) :
    l.min? = Std.DHashMap.Internal.List.min?' l.toListModel := by
  rw [min?_eq_min?ₘ, apply_min?ₘ hlo]

/-!
### `contains`
-/

theorem apply_containsₘ [Ord α] [TransOrd α] {k : α} {l : Impl α β} (hlo : l.Ordered) :
    l.containsₘ k = containsKey k l.toListModel := by
  rw [containsₘ, applyCell_eq_apply_toListModel hlo (fun l _ => containsKey k l)]
  · rintro ⟨(_|p), hp⟩ -
    · simp [Cell.contains]
    · simp only [Cell.contains, Option.isSome_some, Option.toList_some, Bool.true_eq]
      rw [containsKey_cons_of_beq]
      simp [OrientedCmp.eq_symm (hp p rfl)]
  · exact fun l₁ l₂ h a hP => containsKey_of_perm hP
  · exact fun l₁ l₂ h h' => containsKey_append_of_not_contains_right h'

theorem apply_contains [Ord α] [TransOrd α] {k : α} {l : Impl α β} (hlo : l.Ordered) :
    l.contains k = containsKey k l.toListModel := by
  rw [contains_eq_containsₘ, apply_containsₘ hlo]

/-!
## Verification of modification operations
-/

/-!
### `empty`
-/

@[simp]
theorem toListModel_empty : (.empty : Impl α β).toListModel = [] := by
  simp [empty]

theorem ordered_empty [Ord α] : (.empty : Impl α β).Ordered := by
  simp [Ordered]

/-!
### `insertₘ`
-/

theorem ordered_insertₘ [Ord α] [TransOrd α] {k : α} {v : β k} {l : Impl α β} (hlb : l.Balanced)
    (hlo : l.Ordered) : (l.insertₘ k v hlb).Ordered :=
  ordered_updateAtKey _ hlo

theorem toListModel_insertₘ [Ord α] [TransOrd α] {k : α} {v : β k} {l : Impl α β} (hlb : l.Balanced)
    (hlo : l.Ordered) : (l.insertₘ k v hlb).toListModel.Perm (insertEntry k v l.toListModel) := by
  refine toListModel_updateAtKey_perm _ hlo ?_ insertEntry_of_perm
    insertEntry_append_of_not_contains_right
  rintro ⟨(_|l), hl⟩
  · simp
  · simp only [Option.toList_some, Cell.of_inner]
    have h : l.fst == k := by simpa using OrientedCmp.eq_symm (hl l rfl)
    rw [insertEntry_of_containsKey (containsKey_cons_of_beq h), replaceEntry_cons_of_true h]

/-!
### `insert`
-/

theorem ordered_insert [Ord α] [TransOrd α] {k : α} {v : β k} {l : Impl α β} (hlb : l.Balanced)
    (hlo : l.Ordered) : (l.insert k v hlb).impl.Ordered := by
  simpa only [insert_eq_insertₘ] using ordered_insertₘ hlb hlo

theorem toListModel_insert [Ord α] [TransOrd α] {k : α} {v : β k} {l : Impl α β} (hlb : l.Balanced)
    (hlo : l.Ordered) :
    (l.insert k v hlb).impl.toListModel.Perm (insertEntry k v l.toListModel) := by
  rw [insert_eq_insertₘ]
  exact toListModel_insertₘ hlb hlo

/-!
### `insertSlow`
-/

theorem WF.insertSlow [Ord α] [TransOrd α] {k : α} {v : β k} {l : Impl α β}
    (h : l.WF) : (l.insertSlow k v).WF := by
  simpa [insert_eq_insertSlow] using WF.insert (h := h.balanced) h

theorem toListModel_insertSlow [Ord α] [TransOrd α] {k : α} {v : β k} {l : Impl α β}
    (hlb : l.Balanced) (hlo : l.Ordered) :
    (l.insertSlow k v).toListModel.Perm (insertEntry k v l.toListModel) := by
  rw [insertSlow_eq_insertₘ]
  exact toListModel_insertₘ hlb hlo

/-!
## Deducing that well-formed trees are ordered
-/

theorem WF.ordered [Ord α] [TransOrd α] {l : Impl α β} (h : WF l) : l.Ordered := by
  induction h
  · next h => exact h
  · exact ordered_empty
  · exact ordered_insert ‹_› ‹_›

end Std.DTreeMap.Internal.Impl
