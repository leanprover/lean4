/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert
-/
prelude
import Init.Data.Option.List
import Init.Data.Array.Bootstrap
import Std.Classes.Ord
import Std.Data.DTreeMap.Internal.Model
import Std.Data.Internal.Cut
import Std.Data.Internal.List.Associative

/-!
# Lemmas relating operations on well-formed size-bounded trees to operations on lists

This file contains lemmas that relate `Impl.toListModel` to the queries and operations on `Impl`.
The `Impl.Ordered` property, being defined in terms of `Impl.toListModel`, is then shown to be
preserved by all of the operations.

However, this file does not contain lemmas that relate operations besides `Impl.toListModel` to
each other or themselves. Such proofs crucially build on top of the lemmas in this file and
can be found in `Std.Data.Internal.Lemmas`.
-/

set_option autoImplicit false
set_option linter.all true

universe u v w

variable {α : Type u} {β : α → Type v} {γ : α → Type w} {δ : Type w}
private local instance : Coe (Type v) (α → Type v) where coe γ := fun _ => γ

namespace Std.DTreeMap.Internal.Impl
open Std.Internal

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

@[simp]
theorem toListModel_link2 [Ord α] {l r : Impl α β} {hl hr} :
    (l.link2 r hl hr).impl.toListModel = l.toListModel ++ r.toListModel := by
  cases l, r, hl, hr using link2.fun_cases
    <;> simp only [link2, toListModel_leaf, List.nil_append, List.cons_append, List.append_nil]
    <;> split
    <;> (try simp; done)
  all_goals
    simp only [toListModel_balanceLErase, toListModel_balanceRErase]
    rw [toListModel_link2]
    simp
termination_by sizeOf l + sizeOf r

@[simp]
theorem toListModel_insertMin [Ord α] {k v} {t : Impl α β} {h} :
    (t.insertMin k v h).impl.toListModel = ⟨k, v⟩ :: t.toListModel := by
  match t with
  | .leaf => rfl
  | .inner .. => rw [insertMin]; simp [toListModel_insertMin]

@[simp]
theorem toListModel_insertMax [Ord α] {k v} {t : Impl α β} {h} :
    (t.insertMax k v h).impl.toListModel = t.toListModel ++ [⟨k, v⟩] := by
  match t with
  | .leaf => rfl
  | .inner .. => rw [insertMax]; simp [toListModel_insertMax]

@[simp]
theorem toListModel_link [Ord α] {k v} {l r : Impl α β} {hl hr} :
    (l.link k v r hl hr).impl.toListModel = l.toListModel ++ ⟨k, v⟩ :: r.toListModel := by
  cases k, v, l, r, hl, hr using link.fun_cases <;> simp [link] <;> split <;> (try simp; done)
  all_goals
    simp only [toListModel_balanceLErase, toListModel_balanceRErase]
    rw [toListModel_link]
    simp
termination_by sizeOf l + sizeOf r

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

theorem toListModel_filter_gt_of_lt [Ord α] [TransOrd α] {k : α → Ordering} [IsStrictCut compare k]
    {sz k' v' l r} (hcmp : k k' = .lt) (ho : (inner sz k' v' l r).Ordered) :
    (inner sz k' v' l r : Impl α β).toListModel.filter (k ·.1 == .gt) =
      l.toListModel.filter (k ·.1 == .gt) := by
  rw [toListModel_inner, List.filter_append, (List.filter_eq_nil_iff (l := _ :: _)).2,
    List.append_nil]
  simpa [hcmp] using Ordered.compare_right_not_beq_gt ho (Ordering.isLE_of_eq_lt hcmp)

theorem toListModel_find?_of_gt [Ord α] [TransOrd α] {k : α → Ordering} [IsStrictCut compare k]
    {sz k' v' l r} (hcmp : k k' = .gt) (ho : (inner sz k' v' l r).Ordered) :
    (inner sz k' v' l r : Impl α β).toListModel.find? (k ·.1 == .eq) =
      r.toListModel.find? (k ·.1 == .eq) := by
  rw [toListModel_inner, List.find?_append, List.find?_eq_none.2, Option.none_or,
    List.find?_cons_of_neg]
  · simp [hcmp]
  · exact Ordered.compare_left_not_beq_eq ho (Ordering.isGE_of_eq_gt hcmp)

theorem toListModel_find?_of_eq [Ord α] [TransOrd α] {k : α → Ordering} [IsStrictCut compare k]
    {sz k' v' l r} (hcmp : k k' = .eq) (ho : (inner sz k' v' l r).Ordered) :
    (inner sz k' v' l r : Impl α β).toListModel.find? (k ·.1 == .eq) = some ⟨k', v'⟩ := by
  rw [toListModel_inner, List.find?_append, List.find?_eq_none.2, Option.none_or,
    List.find?_cons_of_pos]
  · simp_all
  · exact Ordered.compare_left_not_beq_eq ho (Ordering.isGE_of_eq_eq hcmp)

theorem toListModel_find?_of_lt [Ord α] [TransOrd α] {k : α → Ordering} [IsCut compare k]
    {sz k' v' l r} (hcmp : k k' = .lt) (ho : (inner sz k' v' l r).Ordered) :
    (inner sz k' v' l r : Impl α β).toListModel.find? (k ·.1 == .eq) =
      l.toListModel.find? (k ·.1 == .eq) := by
  rw [toListModel_inner, List.find?_append, Option.or_eq_left_of_none]
  rw [List.find?_cons_of_neg _ (by simp [hcmp])]
  refine List.find?_eq_none.2 (fun p hp => by simp [IsCut.lt hcmp (ho.compare_right hp)])

theorem toListModel_filter_lt_of_gt [Ord α] [TransOrd α] {k : α → Ordering} [IsCut compare k]
    {sz k' v' l r} (hcmp : k k' = .gt) (ho : (inner sz k' v' l r).Ordered) :
    (inner sz k' v' l r : Impl α β).toListModel.filter (k ·.1 == .lt) =
      r.toListModel.filter (k ·.1 == .lt) := by
  rw [toListModel_inner, List.filter_append, List.filter_eq_nil_iff.2, List.nil_append,
    List.filter_cons_of_neg (by simp [hcmp])]
  exact fun p hp => by simp [IsCut.gt hcmp (OrientedCmp.gt_of_lt (ho.compare_left hp))]

theorem toListModel_filter_lt_of_eq [Ord α] [TransOrd α] {k : α → Ordering} [IsStrictCut compare k]
    {sz k' v' l r} (hcmp : k k' = .eq) (ho : (inner sz k' v' l r).Ordered) :
    (inner sz k' v' l r : Impl α β).toListModel.filter (k ·.1 == .lt) = r.toListModel := by
  rw [toListModel_inner, List.filter_append, List.filter_eq_nil_iff.2, List.nil_append,
    List.filter_cons_of_neg (by simp [hcmp]), List.filter_eq_self]
  · exact fun p hp =>
      by simp [IsStrictCut.lt_of_isLE_of_lt (Ordering.isLE_of_eq_eq hcmp) (ho.compare_right hp)]
  · exact fun p hp =>
      by simp [IsStrictCut.gt_of_isGE_of_gt (Ordering.isGE_of_eq_eq hcmp)
          (OrientedCmp.gt_of_lt (ho.compare_left hp))]

theorem toListModel_filter_lt_of_lt [Ord α] [TransOrd α] {k : α → Ordering} [IsCut compare k]
    {sz k' v' l r} (hcmp : k k' = .lt) (ho : (inner sz k' v' l r).Ordered) :
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

theorem findCell_of_gt [Ord α] [TransOrd α] {k : α → Ordering} [IsStrictCut compare k]
    {sz k' v' l r} (hcmp : k k' = .gt) (ho : (inner sz k' v' l r : Impl α β).Ordered) :
    List.findCell (inner sz k' v' l r).toListModel k = List.findCell r.toListModel k :=
  Cell.ext (toListModel_find?_of_gt hcmp ho)

theorem findCell_of_eq [Ord α] [TransOrd α] {k : α → Ordering} [IsStrictCut compare k]
    {sz k' v' l r} (hcmp : k k' = .eq) (ho : (inner sz k' v' l r : Impl α β).Ordered) :
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
  · rename_i sz k' v' l r hb hcmp l' hl'₁ hl'₂ hl'₃ hup ih
    simp only [updateCell, hcmp]
    split <;> rename_i hcmp' <;> try (simp [hcmp] at hcmp'; done)
    rw [toListModel_balance, toListModel_filter_gt_of_lt hcmp hlo,
      toListModel_filter_lt_of_lt hcmp hlo, findCell_of_lt hcmp hlo, ih hlo.left]
    simp
  · rename_i sz k' v' l r hl hcmp hf
    simp only [updateCell, hcmp, hf]
    split <;> rename_i hcmp' <;> try (simp [hcmp] at hcmp'; done)
    rw [toListModel_glue, toListModel_filter_gt_of_eq hcmp hlo, findCell_of_eq hcmp hlo,
      hf, toListModel_filter_lt_of_eq hcmp hlo]
    simp
  · rename_i sz k' v' l r hl hcmp k'' v'' hf
    simp only [updateCell, hcmp, hf]
    split <;> rename_i hcmp' <;> try (simp [hcmp] at hcmp'; done)
    rw [toListModel_inner, toListModel_filter_gt_of_eq hcmp hlo, findCell_of_eq hcmp hlo,
      toListModel_filter_lt_of_eq hcmp hlo, hf]
    simp
  · rename_i sz k' v' l r hb hcmp l' hl'₁ hl'₂ hl'₃ hup ih
    simp only [updateCell, hcmp]
    split <;> rename_i hcmp' <;> try (simp [hcmp] at hcmp'; done)
    rw [toListModel_filter_gt_of_gt hcmp hlo, findCell_of_gt hcmp hlo,
      toListModel_filter_lt_of_gt hcmp hlo, toListModel_balance, ih hlo.right]
    simp

theorem toListModel_eq_append [Ord α] [TransOrd α] (k : α → Ordering) [IsStrictCut compare k]
    {l : Impl α β} (ho : l.Ordered) :
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
    simp only [List.mem_filter, beq_iff_eq, Option.mem_toList, Option.mem_def] at ha hb
    have : compare k b.fst = .eq := (f (List.findCell l.toListModel (compare k))).property _ hb
    exact TransCmp.lt_of_lt_of_eq (OrientedCmp.lt_of_gt ha.2) this
  · intro a ha b hb
    rw [List.mem_append] at ha
    obtain ha|ha := ha
    · exact hlo.2.2 a (List.mem_append_left _ ha) _ hb
    · simp only [Option.mem_toList, Option.mem_def] at ha
      have h₀ : compare k a.fst = .eq := (f (List.findCell l.toListModel (compare k))).property _ ha
      have h₁ : compare k b.fst = .lt := by
        simp only [List.mem_filter, beq_iff_eq] at hb
        exact hb.2
      exact TransCmp.lt_of_eq_of_lt (OrientedCmp.eq_symm h₀) h₁

/-!
## Connecting the tree maps machinery to the hash map machinery
-/

attribute [local instance] beqOfOrd equivBEq_of_transOrd lawfulBEq_of_lawfulEqOrd
attribute [local simp] beq_eq

open Std.Internal.List

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

theorem Ordered.distinctKeys [BEq α] [Ord α] [LawfulBEqOrd α] {l : Impl α β} (h : l.Ordered) :
    DistinctKeys l.toListModel :=
  ⟨by rw [keys_eq_map, List.pairwise_map]; exact h.imp (fun h => by
    simp [← LawfulBEqOrd.not_compare_eq_iff_beq_eq_false, h])⟩

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

theorem contains_findCell [Ord α] [TransOrd α] {k : α → Ordering} [IsStrictCut compare k]
    {l : Impl α β} (hlo : l.Ordered) (h : l.contains' k) :
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
      applyPartition.go k l f ll ℓ h rr = f (l.toListModel.filter (k ·.1 == .gt))
        (List.findCell l.toListModel k) (contains_findCell hlo)
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

theorem containsKey_toListModel [Ord α] [OrientedOrd α] {k : α} {l : Impl α β}
    (h : l.contains' (compare k)) : containsKey k l.toListModel := by
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

theorem applyPartition_eq_apply_toListModel [Ord α] [TransOrd α] {k : α} {l : Impl α β}
    (hlo : l.Ordered)
    {f : List ((a : α) × β a) → (c : Cell α β (compare k)) →
      (l.contains' (compare k) → c.contains) → List ((a : α) × β a) → δ}
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

theorem applyPartition_eq_apply_toListModel' [Ord α] [TransOrd α] {k : α → Ordering}
    [IsStrictCut compare k] {l : Impl α β} (hlo : l.Ordered)
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
    (hg : ∀ l₁ l₂ h, (h' : containsKey k l₂ = false) → g (l₁ ++ l₂) h = g l₁ (by simpa [h'] using h)) :
    applyCell k l f = g l.toListModel containsKey_toListModel := by
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

/-!
### `isEmpty`
-/

theorem isEmpty_eq_isEmpty {t : Impl α β} :
    t.isEmpty = t.toListModel.isEmpty := by
  cases t <;> simp [isEmpty]

/-!
### `size`
-/

theorem size_eq_length (t : Impl α β) (htb : t.Balanced) : t.size = t.toListModel.length := by
  induction t <;> simp [Impl.size]
  rename_i ihl ihr
  cases htb
  rename_i htb
  rw [htb]
  simp only [*]
  ac_rfl

/-!
### `contains`
-/

theorem containsₘ_eq_containsKey [Ord α] [TransOrd α] {k : α} {l : Impl α β} (hlo : l.Ordered) :
    l.containsₘ k = containsKey k l.toListModel := by
  rw [containsₘ, applyCell_eq_apply_toListModel hlo (fun l _ => containsKey k l)]
  · rintro ⟨(_|p), hp⟩ -
    · simp [Cell.contains]
    · simp only [Cell.contains, Option.isSome_some, Option.toList_some, Bool.true_eq]
      rw [containsKey_cons_of_beq]
      simp [OrientedCmp.eq_symm (hp p rfl)]
  · exact fun l₁ l₂ h a hP => containsKey_of_perm hP
  · exact fun l₁ l₂ h h' => containsKey_append_of_not_contains_right h'

theorem contains_eq_containsKey [instBEq : BEq α] [Ord α] [LawfulBEqOrd α] [TransOrd α] {k : α}
    {l : Impl α β} (hlo : l.Ordered) :
    l.contains k = containsKey k l.toListModel := by
  rw [eq_beqOfOrd_of_lawfulBEqOrd instBEq]
  rw [contains_eq_containsₘ, containsₘ_eq_containsKey hlo]

/-!
### `get?`
-/

theorem get?ₘ_eq_getValueCast? [Ord α] [TransOrd α] [LawfulEqOrd α] {k : α} {t : Impl α β}
    (hto : t.Ordered) : t.get?ₘ k = getValueCast? k t.toListModel := by
  rw [get?ₘ, applyCell_eq_apply_toListModel hto (fun l _ => getValueCast? k l)]
  · rintro ⟨(_|p), hp⟩ -
    · simp [Cell.get?]
    · simp only [Cell.get?, Option.toList_some, getValueCast?, beq_eq,
        compare_eq_iff_eq, Option.some_eq_dite_none_right, exists_prop, and_true]
      simp [OrientedCmp.eq_symm (hp p rfl)]
  · exact fun l₁ l₂ h => getValueCast?_of_perm
  · exact fun l₁ l₂ h => getValueCast?_append_of_containsKey_eq_false

theorem get?_eq_getValueCast? [instBEq : BEq α] [Ord α] [i : LawfulBEqOrd α] [TransOrd α]
    [LawfulEqOrd α] {k : α} {t : Impl α β}
    (hto : t.Ordered) : t.get? k = getValueCast? k t.toListModel := by
  cases eq_beqOfOrd_of_lawfulBEqOrd instBEq
  rw [get?_eq_get?ₘ, get?ₘ_eq_getValueCast? hto]

/-!
### `get`
-/

theorem contains_eq_isSome_get?ₘ [Ord α] [TransOrd α] [LawfulEqOrd α] {k : α} {t : Impl α β}
    (hto : t.Ordered) : contains k t = (t.get?ₘ k).isSome := by
  rw [get?ₘ_eq_getValueCast? hto, contains_eq_containsKey hto, containsKey_eq_isSome_getValueCast?]

theorem getₘ_eq_getValueCast [Ord α] [TransOrd α] [LawfulEqOrd α] {k : α} {t : Impl α β} (h) {h'}
    (hto : t.Ordered) : t.getₘ k h' = getValueCast k t.toListModel h := by
  simp only [getₘ]
  revert h'
  rw [get?ₘ_eq_getValueCast? hto]
  simp [getValueCast?_eq_some_getValueCast ‹_›]

theorem get_eq_getValueCast [instBEq : BEq α] [Ord α] [LawfulBEqOrd α] [TransOrd α] [LawfulEqOrd α] {k : α} {t : Impl α β} {h}
    (hto : t.Ordered): t.get k h = getValueCast k t.toListModel (contains_eq_containsKey hto ▸ h) := by
  cases eq_beqOfOrd_of_lawfulBEqOrd instBEq
  rw [get_eq_getₘ, getₘ_eq_getValueCast _ hto]
  exact contains_eq_isSome_get?ₘ hto ▸ h

/-!
### `get!`
-/

theorem get!ₘ_eq_getValueCast! [Ord α] [TransOrd α] [LawfulEqOrd α] {k : α} [Inhabited (β k)]
    {t : Impl α β} (hto : t.Ordered) : t.get!ₘ k = getValueCast! k t.toListModel := by
  simp [get!ₘ, get?ₘ_eq_getValueCast? hto, getValueCast!_eq_getValueCast?]

theorem get!_eq_getValueCast! [instBEq : BEq α] [Ord α] [LawfulBEqOrd α] [TransOrd α] [LawfulEqOrd α] {k : α} [Inhabited (β k)]
    {t : Impl α β} (hto : t.Ordered) : t.get! k = getValueCast! k t.toListModel := by
  cases eq_beqOfOrd_of_lawfulBEqOrd instBEq
  rw [get!_eq_get!ₘ, get!ₘ_eq_getValueCast! hto]

/-!
### `getD`
-/

theorem getDₘ_eq_getValueCastD [Ord α] [TransOrd α] [LawfulEqOrd α] {k : α}
    {t : Impl α β} {fallback : β k} (hto : t.Ordered) :
    t.getDₘ k fallback = getValueCastD k t.toListModel fallback := by
  simp [getDₘ, get?ₘ_eq_getValueCast? hto, getValueCastD_eq_getValueCast?]

theorem getD_eq_getValueCastD [Ord α] [instBEq : BEq α] [LawfulBEqOrd α] [TransOrd α] [LawfulEqOrd α] {k : α}
    {t : Impl α β} {fallback : β k} (hto : t.Ordered) :
    t.getD k fallback = getValueCastD k t.toListModel fallback := by
  cases eq_beqOfOrd_of_lawfulBEqOrd instBEq
  rw [getD_eq_getDₘ, getDₘ_eq_getValueCastD hto]

/-!
### `getKey?`
-/

theorem getKey?ₘ_eq_getKey? [Ord α] [TransOrd α] {k : α} {t : Impl α β}
    (hto : t.Ordered) : t.getKey?ₘ k = List.getKey? k t.toListModel := by
  rw [getKey?ₘ, applyCell_eq_apply_toListModel hto (fun l _ => List.getKey? k l)]
  · rintro ⟨(_|p), hp⟩ -
    · simp [Cell.getKey?]
    · simp only [Cell.getKey?, Option.toList_some, List.getKey?, beq_eq,
        compare_eq_iff_eq, Option.some_eq_dite_none_right, exists_prop, and_true]
      simp [OrientedCmp.eq_symm (hp p rfl)]
  · exact fun l₁ l₂ h => List.getKey?_of_perm
  · exact fun l₁ l₂ h => List.getKey?_append_of_containsKey_eq_false

theorem getKey?_eq_getKey? [Ord α] [TransOrd α] [instBEq : BEq α] [LawfulBEqOrd α] {k : α} {t : Impl α β}
    (hto : t.Ordered) : t.getKey? k = List.getKey? k t.toListModel := by
  cases eq_beqOfOrd_of_lawfulBEqOrd instBEq
  rw [getKey?_eq_getKey?ₘ, getKey?ₘ_eq_getKey? hto]

/-!
### `getKey`
-/

theorem contains_eq_isSome_getKey?ₘ [Ord α] [TransOrd α] {k : α} {t : Impl α β}
    (hto : t.Ordered) : contains k t = (t.getKey?ₘ k).isSome := by
  rw [getKey?ₘ_eq_getKey? hto, contains_eq_containsKey hto, containsKey_eq_isSome_getKey?]

theorem getKeyₘ_eq_getKey [Ord α] [TransOrd α] {k : α} {t : Impl α β} (h) {h'}
    (hto : t.Ordered) : t.getKeyₘ k h' = List.getKey k t.toListModel h := by
  simp only [getKeyₘ]
  revert h'
  rw [getKey?ₘ_eq_getKey? hto]
  simp [getKey?_eq_some_getKey ‹_›]

theorem getKey_eq_getKey [Ord α] [TransOrd α] [instBEq : BEq α] [LawfulBEqOrd α] {k : α} {t : Impl α β} {h}
    (hto : t.Ordered): t.getKey k h = List.getKey k t.toListModel (contains_eq_containsKey hto ▸ h) := by
  cases eq_beqOfOrd_of_lawfulBEqOrd instBEq
  rw [getKey_eq_getKeyₘ, getKeyₘ_eq_getKey _ hto]
  exact contains_eq_isSome_getKey?ₘ hto ▸ h

/-!
### `getKey!`
-/

theorem getKey!ₘ_eq_getKey! [Ord α] [TransOrd α] {k : α} [Inhabited α]
    {t : Impl α β} (hto : t.Ordered) : t.getKey!ₘ k = List.getKey! k t.toListModel := by
  simp [getKey!ₘ, getKey?ₘ_eq_getKey? hto, getKey!_eq_getKey?]

theorem getKey!_eq_getKey! [Ord α] [TransOrd α] [instBEq : BEq α] [LawfulBEqOrd α] {k : α} [Inhabited α]
    {t : Impl α β} (hto : t.Ordered) : t.getKey! k = List.getKey! k t.toListModel := by
  cases eq_beqOfOrd_of_lawfulBEqOrd instBEq
  rw [getKey!_eq_getKey!ₘ, getKey!ₘ_eq_getKey! hto]

/-!
### `getKeyD`
-/

theorem getKeyDₘ_eq_getKeyD [Ord α] [TransOrd α] {k : α}
    {t : Impl α β} {fallback : α} (hto : t.Ordered) :
    t.getKeyDₘ k fallback = List.getKeyD k t.toListModel fallback := by
  simp [getKeyDₘ, getKey?ₘ_eq_getKey? hto, getKeyD_eq_getKey?]

theorem getKeyD_eq_getKeyD [Ord α] [TransOrd α] [instBEq : BEq α] [LawfulBEqOrd α] {k : α}
    {t : Impl α β} {fallback : α} (hto : t.Ordered) :
    t.getKeyD k fallback = List.getKeyD k t.toListModel fallback := by
  cases eq_beqOfOrd_of_lawfulBEqOrd instBEq
  rw [getKeyD_eq_getKeyDₘ, getKeyDₘ_eq_getKeyD hto]

namespace Const

variable {β : Type v}

/-!
### `get?`
-/

theorem get?ₘ_eq_getValue? [Ord α] [TransOrd α] {k : α} {t : Impl α (fun _ => β)} (hto : t.Ordered) :
    get?ₘ t k = getValue? k t.toListModel := by
  rw [get?ₘ, applyCell_eq_apply_toListModel hto (fun l _ => getValue? k l)]
  · rintro ⟨(_|p), hp⟩ -
    · simp [Cell.Const.get?]
    · simp only [Cell.Const.get?, Option.toList_some, getValue?, beq_eq,
        compare_eq_iff_eq, Option.some_eq_dite_none_right, exists_prop, and_true]
      simp [OrientedCmp.eq_symm (hp p rfl)]
  · exact fun l₁ l₂ h => getValue?_of_perm
  · exact fun l₁ l₂ h => getValue?_append_of_containsKey_eq_false

theorem get?_eq_getValue? [Ord α] [TransOrd α] [instBEq : BEq α] [LawfulBEqOrd α] {k : α} {t : Impl α (fun _ => β)} (hto : t.Ordered) :
    get? t k = getValue? k t.toListModel := by
  cases eq_beqOfOrd_of_lawfulBEqOrd instBEq
  rw [get?_eq_get?ₘ, get?ₘ_eq_getValue? hto]

/-!
### `get`
-/

theorem contains_eq_isSome_get?ₘ [Ord α] [TransOrd α] {k : α} {t : Impl α β}
    (hto : t.Ordered) : contains k t = (get?ₘ t k).isSome := by
  rw [get?ₘ_eq_getValue? hto, contains_eq_containsKey hto, containsKey_eq_isSome_getValue?]

theorem getₘ_eq_getValue [Ord α] [TransOrd α] {k : α} {t : Impl α β} (h) {h'}
    (hto : t.Ordered) : getₘ t k h' = getValue k t.toListModel h := by
  simp only [getₘ]
  revert h'
  rw [get?ₘ_eq_getValue? hto]
  simp [getValue?_eq_some_getValue ‹_›]

theorem get_eq_getValue [Ord α] [TransOrd α] [instBEq : BEq α] [LawfulBEqOrd α] {k : α} {t : Impl α β} {h}
    (hto : t.Ordered): get t k h = getValue k t.toListModel (contains_eq_containsKey hto ▸ h) := by
  cases eq_beqOfOrd_of_lawfulBEqOrd instBEq
  rw [get_eq_getₘ, getₘ_eq_getValue _ hto]
  exact contains_eq_isSome_get?ₘ hto ▸ h

/-!
### `get!`
-/

theorem get!ₘ_eq_getValue! [Ord α] [TransOrd α] {k : α} [Inhabited β]
    {t : Impl α β} (hto : t.Ordered) : get!ₘ t k = getValue! k t.toListModel := by
  simp [get!ₘ, get?ₘ_eq_getValue? hto, getValue!_eq_getValue?]

theorem get!_eq_getValue! [Ord α] [TransOrd α] [instBEq : BEq α] [LawfulBEqOrd α] {k : α} [Inhabited β]
    {t : Impl α β} (hto : t.Ordered) : get! t k = getValue! k t.toListModel := by
  cases eq_beqOfOrd_of_lawfulBEqOrd instBEq
  rw [get!_eq_get!ₘ, get!ₘ_eq_getValue! hto]

/-!
### `getD`
-/

theorem getDₘ_eq_getValueD [Ord α] [TransOrd α] {k : α}
    {t : Impl α β} {fallback : β} (hto : t.Ordered) :
    getDₘ t k fallback = getValueD k t.toListModel fallback := by
  simp [getDₘ, get?ₘ_eq_getValue? hto, getValueD_eq_getValue?]

theorem getD_eq_getValueD [Ord α] [TransOrd α] [instBEq : BEq α] [LawfulBEqOrd α] {k : α}
    {t : Impl α β} {fallback : β} (hto : t.Ordered) :
    getD t k fallback = getValueD k t.toListModel fallback := by
  cases eq_beqOfOrd_of_lawfulBEqOrd instBEq
  rw [getD_eq_getDₘ, getDₘ_eq_getValueD hto]

end Const

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
### `insert!`
-/

theorem WF.insert! {_ : Ord α} [TransOrd α] {k : α} {v : β k} {l : Impl α β}
    (h : l.WF) : (l.insert! k v).WF := by
  simpa [insert_eq_insert!] using WF.insert (h := h.balanced) h

theorem toListModel_insert! [instBEq : BEq α] [Ord α] [LawfulBEqOrd α] [TransOrd α] {k : α} {v : β k} {l : Impl α β}
    (hlb : l.Balanced) (hlo : l.Ordered) :
    (l.insert! k v).toListModel.Perm (insertEntry k v l.toListModel) := by
  rw [insert!_eq_insertₘ, eq_beqOfOrd_of_lawfulBEqOrd instBEq]
  exact toListModel_insertₘ hlb hlo

/-!
### `eraseₘ`
-/

theorem ordered_eraseₘ [Ord α] [TransOrd α] {k : α} {t : Impl α β} (htb : t.Balanced)
    (hto : t.Ordered) : (t.eraseₘ k htb).Ordered :=
  ordered_updateAtKey _ hto

theorem toListModel_eraseₘ [Ord α] [TransOrd α] {k : α} {t : Impl α β} (htb : t.Balanced)
    (hto : t.Ordered) : (t.eraseₘ k htb).toListModel.Perm (eraseKey k t.toListModel) := by
  refine toListModel_updateAtKey_perm _ hto ?_ eraseKey_of_perm
    eraseKey_append_of_containsKey_right_eq_false
  rintro ⟨(_|t), hl⟩
  · simp
  · simp only [Option.toList_some, Cell.of_inner]
    have h : t.fst == k := by simpa using OrientedCmp.eq_symm (hl t rfl)
    simp [eraseKey_cons_of_beq h]

/-!
### `erase`
-/

theorem ordered_erase [Ord α] [TransOrd α] {k : α} {t : Impl α β} (htb : t.Balanced)
    (hto : t.Ordered) : (t.erase k htb).impl.Ordered := by
  simpa only [erase_eq_eraseₘ] using ordered_eraseₘ htb hto

theorem toListModel_erase [Ord α] [TransOrd α] {k : α} {t : Impl α β} (htb : t.Balanced)
    (hto : t.Ordered) :
    (t.erase k htb).impl.toListModel.Perm (eraseKey k t.toListModel) := by
  rw [erase_eq_eraseₘ]
  exact toListModel_eraseₘ htb hto

/-!
### `erase!`
-/

theorem WF.erase! {_ : Ord α} [TransOrd α] {k : α} {l : Impl α β}
    (h : l.WF) : (l.erase! k).WF := by
  simpa [erase_eq_erase!] using WF.erase (h := h.balanced) h

theorem toListModel_erase! [Ord α] [TransOrd α] {k : α} {l : Impl α β}
    (hlb : l.Balanced) (hlo : l.Ordered) :
    (l.erase! k).toListModel.Perm (eraseKey k l.toListModel) := by
  rw [erase!_eq_eraseₘ]
  exact toListModel_eraseₘ hlb hlo

/-!
### containsThenInsert
-/

theorem size_containsThenInsert_eq_size [Ord α] (t : Impl α β) :
    containsThenInsert.size t = t.size := by
  induction t <;> rfl

theorem containsThenInsert_fst_eq_containsₘ [Ord α] [TransOrd α] (t : Impl α β) (htb : t.Balanced)
    (ho : t.Ordered) (a : α) (b : β a) :
    (t.containsThenInsert a b htb).1 = t.containsₘ a := by
  simp [containsThenInsert, size_containsThenInsert_eq_size, size_eq_length, htb,
    SizedBalancedTree.balanced_impl _, toListModel_insert htb ho |>.length_eq, length_insertEntry]
  simp [containsₘ_eq_containsKey ho]
  split <;> simp_all

theorem ordered_containsThenInsert [Ord α] [TransOrd α] {k : α} {v : β k} {t : Impl α β}
    (htb : t.Balanced) (hto : t.Ordered) : (t.containsThenInsert k v htb).2.impl.Ordered := by
  simpa only [containsThenInsert_snd_eq_insertₘ, hto] using ordered_insertₘ htb hto

theorem toListModel_containsThenInsert [Ord α] [TransOrd α] {k : α} {v : β k} {t : Impl α β}
    (htb : t.Balanced) (hto : t.Ordered) :
    (t.containsThenInsert k v htb).2.impl.toListModel.Perm (insertEntry k v t.toListModel) := by
  rw [containsThenInsert_snd_eq_insertₘ]
  exact toListModel_insertₘ htb hto

/-!
### containsThenInsert!
-/

theorem WF.containsThenInsert! {_ : Ord α} [TransOrd α] {k : α} {v : β k} {t : Impl α β} (h : t.WF) :
    (t.containsThenInsert! k v).2.WF := by
  simpa [containsThenInsert!_snd_eq_containsThenInsert_snd, h.balanced] using WF.containsThenInsert (h := h.balanced) h

theorem toListModel_containsThenInsert! [Ord α] [TransOrd α] {k : α} {v : β k} {t : Impl α β}
    (htb : t.Balanced) (hto : t.Ordered) :
    (t.containsThenInsert! k v).2.toListModel.Perm (insertEntry k v t.toListModel) := by
  rw [containsThenInsert!_snd_eq_insertₘ]
  exact toListModel_insertₘ htb hto

/-!
### `insertIfNew`
-/

theorem ordered_insertIfNew [Ord α] [TransOrd α] {k : α} {v : β k} {l : Impl α β}
    (h : l.Balanced) (ho : l.Ordered) : (l.insertIfNew k v h).impl.Ordered := by
  simp [Impl.insertIfNew]
  split <;> simp only [ho, ordered_insert h ho]

theorem toListModel_insertIfNew [Ord α] [TransOrd α] {k : α} {v : β k} {l : Impl α β}
    (hlb : l.Balanced) (hlo : l.Ordered) :
    (l.insertIfNew k v hlb).impl.toListModel.Perm (insertEntryIfNew k v l.toListModel) := by
  simp only [Impl.insertIfNew, insertEntryIfNew, cond_eq_if, contains_eq_containsKey hlo]
  split
  · rfl
  · refine (toListModel_insert hlb hlo).trans ?_
    simp [insertEntry_of_containsKey_eq_false, *]

/-!
### `insertIfNew!`
-/

theorem ordered_insertIfNew! [Ord α] [TransOrd α] {k : α} {v : β k} {l : Impl α β}
    (h : l.Balanced) (ho : l.Ordered) : (l.insertIfNew! k v).Ordered := by
  simpa [insertIfNew_eq_insertIfNew!] using ordered_insertIfNew h ho

theorem WF.insertIfNew! {_ : Ord α} [TransOrd α] {k : α} {v : β k} {l : Impl α β}
    (h : l.WF) : (l.insertIfNew! k v).WF := by
  simpa [insertIfNew_eq_insertIfNew!] using h.insertIfNew (h := h.balanced)

theorem toListModel_insertIfNew! [Ord α] [TransOrd α] {k : α} {v : β k} {l : Impl α β}
    (hlb : l.Balanced) (hlo : l.Ordered) :
    (l.insertIfNew! k v).toListModel.Perm (insertEntryIfNew k v l.toListModel) := by
  simpa [insertIfNew_eq_insertIfNew!] using toListModel_insertIfNew hlb hlo

/-!
### containsThenInsertIfNew
-/

theorem ordered_containsThenInsertIfNew [Ord α] [TransOrd α] {k : α} {v : β k} {l : Impl α β}
    (h : l.Balanced) (ho : l.Ordered) : (l.containsThenInsertIfNew k v h).2.impl.Ordered := by
  simpa only [containsThenInsertIfNew_snd_eq_insertIfNew, h] using ordered_insertIfNew h ho

theorem toListModel_containsThenInsertIfNew [Ord α] [TransOrd α] {k : α} {v : β k} {t : Impl α β}
    (htb : t.Balanced) (hto : t.Ordered) :
    (t.containsThenInsertIfNew k v htb).2.impl.toListModel.Perm (insertEntryIfNew k v t.toListModel) := by
  rw [containsThenInsertIfNew_snd_eq_insertIfNew]
  exact toListModel_insertIfNew htb hto

/-!
### containsThenInsertIfNew!
-/

theorem ordered_containsThenInsertIfNew! [Ord α] [TransOrd α] {k : α} {v : β k} {l : Impl α β}
    (h : l.Balanced) (ho : l.Ordered) : (l.containsThenInsertIfNew! k v).2.Ordered := by
  simpa [containsThenInsertIfNew!_snd_eq_insertIfNew!] using ordered_insertIfNew! h ho

theorem WF.containsThenInsertIfNew! {_ : Ord α} [TransOrd α] {k : α} {v : β k} {l : Impl α β}
    (h : l.WF) : (l.containsThenInsertIfNew! k v).2.WF := by
  simpa [containsThenInsertIfNew!_snd_eq_insertIfNew!] using WF.insertIfNew! (h := h)

theorem toListModel_containsThenInsertIfNew! [Ord α] [TransOrd α] {k : α} {v : β k} {t : Impl α β}
    (htb : t.Balanced) (hto : t.Ordered) :
    (t.containsThenInsertIfNew k v htb).2.impl.toListModel.Perm (insertEntryIfNew k v t.toListModel) := by
  rw [containsThenInsertIfNew_snd_eq_insertIfNew]
  exact toListModel_insertIfNew htb hto

/-!
### filterMap
-/

@[simp]
theorem toListModel_filterMap [Ord α] {t : Impl α β} {h} {f : (a : α) → β a → Option (γ a)} :
    (t.filterMap f h).impl.toListModel = t.toListModel.filterMap fun x => (f x.1 x.2).map (⟨x.1, ·⟩) := by
  induction t with
  | leaf => rfl
  | inner sz k v _ _ ihl ihr =>
    simp [filterMap]
    cases h : f k v
    all_goals simp [h, ihl, ihr]

theorem balanced_filterMap [Ord α] {t : Impl α β} {h} {f : (a : α) → β a → Option (γ a)} :
    (t.filterMap f h).impl.Balanced := by apply BalancedTree.balanced_impl

theorem ordered_filterMap [Ord α] {t : Impl α β} {h} {f : (a : α) → β a → Option (γ a)}
    (ho : t.Ordered) : (t.filterMap f h).impl.Ordered := by
  simp only [Ordered, toListModel_filterMap]
  apply ho.filterMap
  intro e f hef e' he' f' hf'
  simp only [Option.mem_def, Option.map_eq_some'] at he' hf'
  obtain ⟨_, _, rfl⟩ := he'
  obtain ⟨_, _, rfl⟩ := hf'
  exact hef

/-!
### filter
-/

theorem filter_eq_filterMap [Ord α] {t : Impl α β} {h} {f : (a : α) → β a → Bool} :
    t.filter f h = t.filterMap (fun k v => if f k v then some v else none) h := by
  induction t with
  | leaf => rfl
  | inner sz k v l r ihl ihr =>
    simp [filter, filterMap]
    cases hf : f k v <;> rw [ihl, ihr] <;> rfl

theorem ordered_filter [Ord α] {t : Impl α β} {h} {f : (a : α) → β a → Bool} (hto : t.Ordered) :
    (t.filter f h).impl.Ordered := by
  simpa only [filter_eq_filterMap] using ordered_filterMap hto

/-!
### alter
-/

theorem toListModel_alterₘ [Ord α] [TransOrd α] [LawfulEqOrd α] {t : Impl α β} {a f}
    (htb : t.Balanced) (hto : t.Ordered) :
    List.Perm ((t.alterₘ a f htb).toListModel) (alterKey a f t.toListModel) := by
  refine toListModel_updateAtKey_perm _ hto ?_ alterKey_of_perm
    alterKey_append_of_containsKey_right_eq_false
  rintro ⟨(_|l), hl⟩
  · simp [Cell.alter, Cell.ofOption]
    cases f none <;> rfl
  · simp only [Cell.alter, Cell.ofOption, alterKey, Option.toList_some]
    have h : a = l.fst := compare_eq_iff_eq.mp <| hl l rfl
    cases h
    simp only [getValueCast?, beq_self_eq_true, ↓reduceDIte, cast_eq]
    cases f _
    · simp [eraseKey]
    · simp [insertEntry, containsKey, replaceEntry]

theorem alter_eq_alterₘ [Ord α] [TransOrd α] [LawfulEqOrd α] {t : Impl α β} {a f}
    (htb : t.Balanced) (hto : t.Ordered) :
    (t.alter a f htb).impl = t.alterₘ a f htb := by
  rw [alterₘ]
  induction t with
  | leaf =>
    simp only [alter, updateCell, Cell.alter, Cell.empty_inner, Cell.ofOption]
    cases f none
    · simp [Cell.of_inner]
    · simp
  | inner sz k v l r ihl ihr =>
    rw [alter, updateCell]
    split <;> rename_i heq <;> simp only [heq]
    · simp [ihl htb.left hto.left]
      split <;> simp_all
    · simp [ihr htb.right hto.right]
      split <;> simp_all
    · apply Eq.symm
      split <;> (try simp_all; done)
      simp [Cell.alter, Cell.ofOption, cast]
      cases h₁ : f _ <;> rfl

theorem toListModel_alter [Ord α] [TransOrd α] [LawfulEqOrd α] {t : Impl α β} {a f}
    (htb : t.Balanced) (hto : t.Ordered) :
    List.Perm (t.alter a f htb).impl.toListModel (alterKey a f t.toListModel) := by
  simpa only [alter_eq_alterₘ, htb, hto] using toListModel_alterₘ htb hto

theorem ordered_alter [Ord α] [TransOrd α] [LawfulEqOrd α] {t : Impl α β} {a f}
    (htb : t.Balanced) (hto : t.Ordered) : (t.alter a f htb).impl.Ordered := by
  rw [alter_eq_alterₘ htb hto, alterₘ]
  exact ordered_updateAtKey htb hto

/-!
### alter!
-/

theorem alter_eq_alter! [Ord α] [LawfulEqOrd α] {t : Impl α β} {a f} (htb) :
    (alter a f t htb).impl = alter! a f t := by
  induction t with
  | leaf =>
    rw [alter, alter!]
    cases f none <;> rfl
  | inner sz k' v' l' r' ihl ihr =>
    rw [alter, alter!]
    split
    case h_1 => simp only [balance_eq_balance!, ihl htb.left]
    case h_2 => simp only [balance_eq_balance!, ihr htb.right]
    case h_3 =>
      cases f (some _)
      · exact glue_eq_glue!
      · rfl

/-!
### modify
-/

theorem modify_eq_alter [Ord α] [LawfulEqOrd α] {t : Impl α β} {a f}
    (htb : t.Balanced) :
    modify a f t = (alter a (·.map f) t htb).impl := by
  induction t with
  | leaf => rfl
  | inner sz k v l r ihl ihr =>
    have hmb : (modify a f _).Balanced := balanced_modify htb
    rw [modify, alter] at *
    split at * <;> try rfl
    all_goals
      simp only [← ihl htb.left, ← ihr htb.right, balance_eq_inner, balance_eq_inner hmb]

theorem ordered_modify [Ord α] [TransOrd α] [LawfulEqOrd α] {t : Impl α β} {a f}
    (htb : t.Balanced) (hto : t.Ordered) : (modify a f t).Ordered :=
  modify_eq_alter htb ▸ ordered_alter htb hto

/-!
### mergeWith
-/

theorem ordered_mergeWith [Ord α] [TransOrd α] [LawfulEqOrd α] {t₁ t₂ : Impl α β} {f}
    (htb : t₁.Balanced) (hto : t₁.Ordered) :
    (t₁.mergeWith f t₂ htb).impl.Ordered := by
  induction t₂ generalizing t₁ with
  | leaf => exact hto
  | inner sz k v l r ihl ihr => exact ihr _ (ordered_alter _ (ihl htb hto))

/-!
### foldlM
-/

theorem foldlM_eq_foldlM_toListModel {t : Impl α β} {m δ} [Monad m] [LawfulMonad m]
    {f : δ → (a : α) → β a → m δ} {init} :
    t.foldlM (init := init) f = t.toListModel.foldlM (init := init) fun acc p => f acc p.1 p.2 := by
  induction t generalizing init with
  | leaf => rfl
  | inner sz k v l r ihl ihr =>
    simp only [foldlM, toListModel_inner, List.foldl_append, List.foldl_cons]
    simp [ihl, ihr]

theorem foldlM_toListModel_eq_foldlM {t : Impl α β} {m δ} [Monad m] [LawfulMonad m]
    {f : δ → ((a : α) × β a) → m δ} {init} :
    t.toListModel.foldlM (init := init) f = t.foldlM (init := init) fun acc k v => f acc ⟨k, v⟩ := by
  rw [foldlM_eq_foldlM_toListModel]

/-!
### foldl
-/

theorem foldl_eq_foldl {t : Impl α β} {δ} {f : δ → (a : α) → β a → δ} {init} :
    t.foldl (init := init) f = t.toListModel.foldl (init := init) fun acc p => f acc p.1 p.2 := by
  rw [foldl, foldlM_eq_foldlM_toListModel, List.foldl_eq_foldlM, Id.run]

/-!
### foldrM
-/

theorem foldrM_eq_foldrM {t : Impl α β} {m δ} [Monad m] [LawfulMonad m]
    {f : (a : α) → β a → δ → m δ} {init} :
    t.foldrM (init := init) f = t.toListModel.foldrM (init := init) fun p acc => f p.1 p.2 acc := by
  induction t generalizing init with
  | leaf => rfl
  | inner sz k v l r ihl ihr =>
    simp only [foldrM, toListModel_inner, List.foldr_append, List.foldr_cons]
    simp [ihl, ihr]

/-!
### foldr
-/

theorem foldr_eq_foldr {t : Impl α β} {δ} {f : (a : α) → β a → δ → δ} {init} :
    t.foldr (init := init) f = t.toListModel.foldr (init := init) fun p acc => f p.1 p.2 acc := by
  rw [foldr, foldrM_eq_foldrM, List.foldr_eq_foldrM, Id.run]

/-!
### toList
-/

theorem toList_eq_toListModel {t : Impl α β} :
    t.toList = t.toListModel := by
  rw [toList, foldr_eq_foldr]
  induction t with
  | leaf => rfl
  | inner sz k v l r ihl ihr => simp

/-!
### keys
-/

theorem keys_eq_keys {t : Impl α β} :
    t.keys = t.toListModel.keys := by
  rw [keys, foldr_eq_foldr, List.keys.eq_def]
  simp
  induction t.toListModel with
  | nil => rfl
  | cons e es ih =>
    simp [ih]
    rw [List.keys.eq_def]

/-!
### forM
-/

theorem forM_eq_forM {t: Impl α β} {m : Type w → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → β a → m PUnit} :
    t.forM f = t.toListModel.forM (fun a => f a.1 a.2) := by
  simp only [Impl.forM, foldlM_eq_foldlM_toListModel]
  induction t.toListModel with
  | nil => rfl
  | cons e es ih => simp [ih]

/-!
### forIn
-/

theorem forInStep_eq_foldlM {δ : Type w} {t : Impl α β} {m : Type w → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → β a → δ → m (ForInStep δ)} {init : δ} :
    t.forInStep f init = t.foldlM (init := .yield init) fun
      | .yield d => fun k v => f k v d
      | .done d => fun _ _ => pure (.done d) := by
  induction t generalizing init with
  | leaf => simp only [forInStep, foldlM]
  | inner sz k v l r ihl ihr =>
    simp [forInStep, foldlM, ihl, ihr]
    congr; ext step
    cases step
    case yield =>
      simp
      congr; ext step
      cases step
      · simp
        clear ihl ihr
        apply Eq.symm
        induction r <;> simp [foldlM, *]
      · simp
    case done =>
      simp only [pure_bind]
      clear ihl ihr
      apply Eq.symm
      induction r <;> simp [foldlM, *]


theorem forIn_eq_forIn_toListModel {δ : Type w} {t : Impl α β} {m : Type w → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → β a → δ → m (ForInStep δ)} {init : δ} :
    t.forIn f init = ForIn.forIn t.toListModel init (fun a d => f a.1 a.2 d) := by
  rw [Impl.forIn, forInStep_eq_foldlM, List.forIn_eq_foldlM, foldlM_eq_foldlM_toListModel]
  induction t.toListModel with
  | nil => simp
  | cons e es ih =>
    simp only [List.foldlM_cons, bind_assoc, map_bind, map_eq_pure_bind]
    congr; ext step
    congr <;> ext step' <;> cases step' <;> rfl

namespace Const

variable {β : Type v}

/-!
### getThenInsertIfNew?!
-/

theorem WF.getThenInsertIfNew?! [Ord α] [TransOrd α] [LawfulEqOrd α] {k : α} {v : β} {t : Impl α β}
    (h : t.WF) : (getThenInsertIfNew?! t k v).2.WF := by
  rw [getThenInsertIfNew?!.eq_def]
  cases get? t k
  · exact h.insertIfNew!
  · exact h

/-!
### alter
-/

theorem toListModel_alterₘ [Ord α] [TransOrd α] {t : Impl α β} {a f}
    (htb : t.Balanced) (hto : t.Ordered) :
    List.Perm ((alterₘ a f t htb).toListModel) (Const.alterKey a f t.toListModel) := by
  refine toListModel_updateAtKey_perm _ hto ?_ Const.alterKey_of_perm
    Const.alterKey_append_of_containsKey_right_eq_false
  rintro ⟨(_|l), hl⟩
  · simp [Cell.Const.alter, Cell.ofOption]
    cases f none <;> rfl
  · simp only [Cell.Const.alter, Cell.ofOption, Const.alterKey, Option.toList_some]
    have := OrientedCmp.eq_symm <| hl l rfl
    simp only [getValue?, beq_eq, this, beq_self_eq_true, cond_eq_if, reduceIte]
    cases f _
    · simp [eraseKey, this]
    · simp [insertEntry, containsKey, replaceEntry, this]

theorem alter_eq_alterₘ [Ord α] [TransOrd α] {t : Impl α β} {a f}
    (htb : t.Balanced) (hto : t.Ordered) :
    (alter a f t htb).impl = alterₘ a f t htb := by
  rw [alterₘ]
  induction t with
  | leaf =>
    simp only [alter, updateCell, Cell.Const.alter, Cell.empty_inner, Cell.ofOption]
    cases f none
    · simp [Cell.of_inner]
    · simp
  | inner sz k v l r ihl ihr =>
    rw [alter, updateCell]
    split <;> rename_i heq <;> simp only [heq]
    · simp [ihl htb.left hto.left]
      split <;> simp_all
    · simp [ihr htb.right hto.right]
      split <;> simp_all
    · apply Eq.symm
      split <;> (try simp_all; done)
      simp [Cell.Const.alter, Cell.ofOption, cast]
      cases h₁ : f _ <;> rfl

theorem toListModel_alter [Ord α] [TransOrd α] {t : Impl α β} {a f}
    (htb : t.Balanced) (hto : t.Ordered) :
    List.Perm (alter a f t htb).impl.toListModel (Const.alterKey a f t.toListModel) := by
  simpa only [alter_eq_alterₘ, htb, hto] using toListModel_alterₘ htb hto

theorem ordered_alter [Ord α] [TransOrd α] {t : Impl α β} {a f}
    (htb : t.Balanced) (hto : t.Ordered) : (alter a f t htb).impl.Ordered := by
  rw [alter_eq_alterₘ htb hto, alterₘ]
  exact ordered_updateAtKey htb hto

/-!
### alter!
-/

theorem alter_eq_alter! [Ord α] {t : Impl α β} {a f} (htb) :
    (alter a f t htb).impl = alter! a f t := by
  induction t with
  | leaf =>
    rw [alter, alter!]
    cases f none <;> rfl
  | inner sz k' v' l' r' ihl ihr =>
    rw [alter, alter!]
    cases compare a k'
    case lt => simp only [balance_eq_balance!, ihl htb.left]
    case gt => simp only [balance_eq_balance!, ihr htb.right]
    case eq =>
      cases f (some v')
      · exact glue_eq_glue!
      · rfl

/-!
### modify
-/

theorem modify_eq_alter [Ord α] [TransOrd α] {t : Impl α β} {a f}
    (htb : t.Balanced) :
    modify a f t = (alter a (·.map f) t htb).impl := by
  induction t with
  | leaf => rfl
  | inner sz k v l r ihl ihr =>
    have hmb : (modify a f _).Balanced := balanced_modify htb
    rw [modify, alter] at *
    split at * <;> try rfl
    all_goals
      dsimp
      simp only [← ihl htb.left, ← ihr htb.right, balance_eq_inner, balance_eq_inner hmb]

theorem ordered_modify [Ord α] [TransOrd α] {t : Impl α β} {a f}
    (htb : t.Balanced) (hto : t.Ordered) : (modify a f t).Ordered :=
  modify_eq_alter htb ▸ ordered_alter htb hto

/-!
### mergeWith
-/

theorem ordered_mergeWith [Ord α] [TransOrd α] {t₁ t₂ : Impl α β} {f}
    (htb : t₁.Balanced) (hto : t₁.Ordered) :
    (mergeWith f t₁ t₂ htb).impl.Ordered := by
  induction t₂ generalizing t₁ with
  | leaf => exact hto
  | inner sz k v l r ihl ihr => exact ihr _ (ordered_alter _ (ihl htb hto))

/-!
### toList
-/

theorem toList_eq_toListModel_map {t : Impl α β} :
    Const.toList t = t.toListModel.map fun ⟨k, v⟩ => (k, v) := by
  rw [toList, foldr_eq_foldr]
  induction t with
  | leaf => rfl
  | inner sz k v l r ihl ihr => simp

end Const

/-!
## Deducing that well-formed trees are ordered
-/

theorem WF.ordered [Ord α] [TransOrd α] {l : Impl α β} (h : WF l) : l.Ordered := by
  induction h
  · next h => exact h
  · exact ordered_empty
  · exact ordered_insert ‹_› ‹_›
  · exact ordered_insertIfNew ‹_› ‹_›
  · exact ordered_erase ‹_› ‹_›
  · exact ordered_alter ‹_› ‹_›
  · exact Const.ordered_alter ‹_› ‹_›
  · exact ordered_modify (WF.balanced ‹_›) ‹_›
  · exact Const.ordered_modify (WF.balanced ‹_›) ‹_›
  · exact ordered_containsThenInsert ‹_› ‹_›
  · exact ordered_containsThenInsertIfNew ‹_› ‹_›
  · exact ordered_filter ‹_›
  · exact ordered_mergeWith ‹_› ‹_›
  · exact Const.ordered_mergeWith ‹_› ‹_›

/-!
## Deducing that additional operations are well-formed
-/

variable {β'} in
/-- Internal implementation detail of the tree map -/
inductive SameKeys : Impl α β → Impl α β' → Prop where
/-- Internal implementation detail of the tree map -/
| leaf : SameKeys .leaf .leaf
/-- Internal implementation detail of the tree map -/
| inner (sz k v v' r r' l l') : SameKeys r r' → SameKeys l l' →
    SameKeys (.inner sz k v l r) (.inner sz k v' l' r')

namespace SameKeys

variable {β'}

theorem ordered_iff_pairwise_keys [Ord α] {t : Impl α β} :
    t.Ordered ↔ List.Pairwise (compare · · = .lt) (t.toListModel.map (·.fst)) := by
  simp [Ordered, List.pairwise_map]

theorem symm [Ord α] {t : Impl α β} {t' : Impl α β'} (hs : SameKeys t t') :
    SameKeys t' t := by
  induction hs with
  | leaf => exact .leaf
  | inner => apply SameKeys.inner <;> assumption

theorem keys_eq [Ord α] {t : Impl α β} {t' : Impl α β'} (h : SameKeys t t') :
    t.toListModel.map (·.fst) = t'.toListModel.map (·.fst) := by
  induction h with
  | leaf => rfl
  | inner => simp_all

theorem size_eq [Ord α] {t : Impl α β} {t' : Impl α β'} (h : SameKeys t t') :
    t.size = t'.size := by
  cases h <;> rfl

theorem ordered [Ord α] {t : Impl α β} {t' : Impl α β'} (hs : SameKeys t t') (h : t.Ordered) :
    t'.Ordered := by
  simp_all only [ordered_iff_pairwise_keys, ← hs.keys_eq]

theorem balanced [Ord α] {t : Impl α β} {t' : Impl α β'} (hs : SameKeys t t') (h : t.Balanced) :
    t'.Balanced := by
  induction hs with
  | leaf => exact .leaf
  | inner _ _ _ _ _ _ _ _ hsr hsl =>
    have := hsl.size_eq
    have := hsr.size_eq
    cases h
    apply Balanced.inner <;> simp_all

theorem wf [Ord α] {t : Impl α β} {t' : Impl α β'} (hs : SameKeys t t') (h : t.WF) : t'.WF :=
  .wf (hs.balanced h.balanced) (hs.ordered h.ordered)

end SameKeys

/-!
### getThenInsertIfNew?!
-/

theorem WF.getThenInsertIfNew?! {_ : Ord α} [TransOrd α] [LawfulEqOrd α] {k : α} {v : β k} {t : Impl α β}
    (h : t.WF) : (t.getThenInsertIfNew?! k v).2.WF := by
  rw [getThenInsertIfNew?!.eq_def]
  cases get? t k
  · exact h.insertIfNew!
  · exact h

theorem WF.constGetThenInsertIfNew?! {β : Type v} {_ : Ord α} [TransOrd α] {k : α} {v : β} {t : Impl α β}
    (h : t.WF) : (Const.getThenInsertIfNew?! t k v).2.WF := by
  rw [Const.getThenInsertIfNew?!.eq_def]
  cases Const.get? t k
  · exact h.insertIfNew!
  · exact h

/-!
### `eraseMany!`
-/

theorem WF.eraseMany! {_ : Ord α} [TransOrd α] {ρ} [ForIn Id ρ α] {l : ρ}
    {t : Impl α β} (h : t.WF) : (t.eraseMany! l).1.WF :=
  (t.eraseMany! l).2 h (fun _ _ h' => h'.erase!)

/-!
### `insertMany`
-/

theorem insertMany!_eq_foldl {_ : Ord α} {l : List ((a : α) × β a)} {t : Impl α β} :
    (t.insertMany! l).val = l.foldl (init := t) fun acc ⟨k, v⟩ => acc.insert! k v := by
  simp [insertMany!, Id.run, ← List.foldl_hom Subtype.val]

theorem insertMany_eq_foldl {_ : Ord α} {l : List ((a : α) × β a)} {t : Impl α β} (h : t.Balanced) :
    (t.insertMany l h).val = l.foldl (init := t) fun acc ⟨k, v⟩ => acc.insert! k v := by
  simp [insertMany, Id.run, insert_eq_insert!, ← List.foldl_hom Subtype.val]

theorem insertMany_eq_insertMany! {_ : Ord α} {l : List ((a : α) × β a)}
    {t : Impl α β} (h : t.Balanced) :
    (t.insertMany l h).val = (t.insertMany! l).val := by
  simp only [insertMany_eq_foldl, insertMany!_eq_foldl]

theorem toListModel_insertMany_list {_ : Ord α} [BEq α] [LawfulBEqOrd α] [TransOrd α]
    {l : List ((a : α) × β a)}
    {t : Impl α β} (h : t.WF) :
    List.Perm (t.insertMany l h.balanced).val.toListModel (t.toListModel.insertList l) := by
  simp only [insertMany_eq_foldl]
  induction l generalizing t with
  | nil => rfl
  | cons e es ih =>
    refine (ih h.insert!).trans ?_
    exact insertList_perm_of_perm_first (toListModel_insert! h.balanced h.ordered)
      h.insert!.ordered.distinctKeys

theorem toListModel_insertMany!_list {_ : Ord α} [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} {t : Impl α β} (h : t.WF) :
    List.Perm (t.insertMany! l).val.toListModel (t.toListModel.insertList l) := by
  simpa only [← insertMany_eq_insertMany! h.balanced] using toListModel_insertMany_list h

theorem WF.insertMany! {_ : Ord α} [TransOrd α] {ρ} [ForIn Id ρ ((a : α) × β a)] {l : ρ}
    {t : Impl α β} (h : t.WF) : (t.insertMany! l).1.WF :=
  (t.insertMany! l).2 h (fun _ _ _ h' => h'.insert!)

theorem WF.constInsertMany! {β : Type v} {_ : Ord α} [TransOrd α] {ρ} [ForIn Id ρ (α × β)] {l : ρ}
    {t : Impl α β} (h : t.WF) : (Const.insertMany! t l).1.WF :=
  (Const.insertMany! t l).2 h (fun _ _ _ h' => h'.insert!)

theorem WF.constInsertManyIfNewUnit! {_ : Ord α} [TransOrd α] {ρ} [ForIn Id ρ α] {l : ρ}
    {t : Impl α Unit} (h : t.WF) : (Const.insertManyIfNewUnit! t l).1.WF :=
  (Const.insertManyIfNewUnit! t l).2 h (fun _ _ h' => h'.insertIfNew!)

namespace Const

variable {β : Type v}

/-!
### `insertMany`
-/

theorem insertMany!_eq_foldl {_ : Ord α} {l : List (α × β)} {t : Impl α β} :
    (insertMany! t l).val = l.foldl (init := t) fun acc ⟨k, v⟩ => acc.insert! k v := by
  simp only [insertMany!, Id.run, Id.pure_eq, Id.bind_eq, List.forIn_yield_eq_foldl]
  rw [← List.foldl_hom Subtype.val]
  simp only [implies_true]

theorem insertMany_eq_foldl {_ : Ord α} {l : List (α × β)}
    {t : Impl α β} (h : t.Balanced) :
    (Const.insertMany t l h).val = l.foldl (init := t) fun acc ⟨k, v⟩ => acc.insert! k v := by
  simp only [insertMany, Id.run, Id.pure_eq, insert_eq_insert!, Id.bind_eq,
    List.forIn_yield_eq_foldl]
  rw [← List.foldl_hom Subtype.val]
  simp only [implies_true]

theorem insertMany_eq_insertMany! {_ : Ord α} {l : List (α × β)}
    {t : Impl α β} (h : t.Balanced) :
    (Const.insertMany t l h).val = (Const.insertMany! t l).val := by
  simp only [insertMany!_eq_foldl, insertMany_eq_foldl]

theorem toListModel_insertMany_list {_ : Ord α} [BEq α] [TransOrd α] [LawfulBEqOrd α]
    {l : List (α × β)} {t : Impl α β} (h : t.WF) :
    List.Perm (Const.insertMany t l h.balanced).val.toListModel (t.toListModel.insertListConst l) := by
  simp only [insertMany_eq_foldl]
  induction l generalizing t with
  | nil => rfl
  | cons e es ih =>
    refine (ih h.insert!).trans ?_
    exact insertList_perm_of_perm_first (toListModel_insert! h.balanced h.ordered)
      h.insert!.ordered.distinctKeys

theorem toListModel_insertMany!_list {_ : Ord α} [BEq α] [LawfulBEqOrd α] [TransOrd α]
    {l : List (α × β)} {t : Impl α β} (h : t.WF) :
    List.Perm (Const.insertMany! t l).val.toListModel (t.toListModel.insertListConst l) := by
  simpa only [← insertMany_eq_insertMany! h.balanced] using toListModel_insertMany_list h

theorem insertManyIfNewUnit_eq_foldl {_ : Ord α} {l : List α} {t : Impl α Unit} (h : t.Balanced) :
    (Const.insertManyIfNewUnit t l h).val = l.foldl (init := t) fun acc k => acc.insertIfNew! k () := by
  simp only [insertManyIfNewUnit, Id.run, Id.pure_eq, Id.bind_eq, List.forIn_yield_eq_foldl]
  rw [← List.foldl_hom Subtype.val]
  simp only [insertIfNew_eq_insertIfNew!, implies_true]

theorem insertManyIfNewUnit!_eq_foldl {_ : Ord α} {l : List α} {t : Impl α Unit} :
    (Const.insertManyIfNewUnit! t l).val = l.foldl (init := t) fun acc k => acc.insertIfNew! k () := by
  simp only [insertManyIfNewUnit!, Id.run, Id.pure_eq, Id.bind_eq, List.forIn_yield_eq_foldl]
  rw [← List.foldl_hom Subtype.val]
  simp only [implies_true]

theorem insertManyIfNewUnit_eq_insertManyIfNewUnit! {_ : Ord α} {l : List α}
    {t : Impl α Unit} (h : t.Balanced) :
    (Const.insertManyIfNewUnit t l h).val = (Const.insertManyIfNewUnit! t l).val := by
  simp only [insertManyIfNewUnit_eq_foldl, insertManyIfNewUnit!_eq_foldl]

theorem toListModel_insertManyIfNewUnit_list {_ : Ord α} [TransOrd α] [instBEq : BEq α]
    [LawfulBEqOrd α] {l : List α} {t : Impl α Unit} (h : t.WF) :
    List.Perm (Const.insertManyIfNewUnit t l h.balanced).val.toListModel
      (t.toListModel.insertListIfNewUnit l) := by
  cases eq_beqOfOrd_of_lawfulBEqOrd instBEq
  simp only [insertManyIfNewUnit_eq_foldl]
  induction l generalizing t with
  | nil => rfl
  | cons e es ih =>
    refine (ih h.insertIfNew!).trans ?_
    exact insertListIfNewUnit_perm_of_perm_first (toListModel_insertIfNew! h.balanced h.ordered)
      h.insertIfNew!.ordered.distinctKeys

theorem toListModel_insertManyIfNewUnit!_list {_ : Ord α} [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List α} {t : Impl α Unit} (h : t.WF) :
    List.Perm (Const.insertManyIfNewUnit! t l).val.toListModel (t.toListModel.insertListIfNewUnit l) := by
  simpa only [← insertManyIfNewUnit_eq_insertManyIfNewUnit! h.balanced] using
    toListModel_insertManyIfNewUnit_list h

end Const

/-!
### alter!
-/

theorem WF.alter! {_ : Ord α} [LawfulEqOrd α] {t : Impl α β} {a f} (h : t.WF) :
    (alter! a f t).WF := by
  rw [← alter_eq_alter! h.balanced]
  exact h.alter

theorem WF.constAlter! {_ : Ord α} {β : Type v} {t : Impl α β} {a f} (h : t.WF) :
    (Const.alter! a f t).WF := by
  rw [← Const.alter_eq_alter! h.balanced]
  exact h.constAlter

/-!
### mergeWith!
-/

theorem mergeWith_eq_mergeWith! {_ : Ord α} [LawfulEqOrd α] {mergeFn} {t₁ t₂ : Impl α β}
    (h : t₁.Balanced) :
    (mergeWith mergeFn t₁ t₂ h).impl = mergeWith! mergeFn t₁ t₂ := by
  rw [mergeWith, mergeWith!]
  induction t₂ generalizing t₁ with
  | leaf => rfl
  | inner sz k v l r ihl ihr =>
    simp only [foldl, foldlM, Id.run, bind]
    simp only [foldl, Id.run, bind] at ihl ihr
    rw [ihr]
    congr
    simp only [SizedBalancedTree.toBalancedTree]
    rw [alter_eq_alter!]
    congr
    exact ihl h

theorem WF.mergeWith! {_ : Ord α} [LawfulEqOrd α] {mergeFn} {t₁ t₂ : Impl α β} (h : t₁.WF) :
    (Impl.mergeWith! mergeFn t₁ t₂).WF := by
  rw [← mergeWith_eq_mergeWith! h.balanced]
  exact h.mergeWith

theorem Const.mergeWith_eq_mergeWith! {β : Type v} {_ : Ord α} {mergeFn} {t₁ t₂ : Impl α β}
    (h : t₁.Balanced) :
    (mergeWith mergeFn t₁ t₂ h).impl = mergeWith! mergeFn t₁ t₂ := by
  rw [mergeWith, mergeWith!]
  induction t₂ generalizing t₁ with
  | leaf => rfl
  | inner sz k v l r ihl ihr =>
    simp only [foldl, foldlM, Id.run, bind]
    simp only [foldl, Id.run, bind] at ihl ihr
    rw [ihr]
    congr
    simp only [SizedBalancedTree.toBalancedTree]
    rw [alter_eq_alter!]
    congr
    exact ihl h

theorem WF.constMergeWith! {β : Type v} {_ : Ord α} {mergeFn} {t₁ t₂ : Impl α β} (h : t₁.WF) :
    (Impl.Const.mergeWith! mergeFn t₁ t₂).WF := by
  rw [← Const.mergeWith_eq_mergeWith! h.balanced]
  exact h.constMergeWith

/-!
### filterMap
-/

theorem WF.filterMap [Ord α] {t : Impl α β} {h} {f : (a : α) → β a → Option (γ a)} (hwf : t.WF) :
    (t.filterMap f h).impl.WF :=
  .wf balanced_filterMap (ordered_filterMap hwf.ordered)

/-!
### filterMap!
-/

theorem filterMap_eq_filterMap! [Ord α] {t : Impl α β} {h} {f : (a : α) → β a → Option (γ a)} :
    (t.filterMap f h).impl = t.filterMap! f := by
  induction t with
  | leaf => rfl
  | inner sz k v _ _ ihl ihr =>
    simp [filterMap, filterMap!]
    cases f k v
    · simp only [link2_eq_link2!, ihl, ihr, h.left, h.right]
    · simp only [link_eq_link!, ihl, ihr, h.left, h.right]

theorem WF.filterMap! {_ : Ord α} {t : Impl α β} {f : (a : α) → β a → Option (γ a)} (h : t.WF) :
    (t.filterMap! f).WF := by
  rw [← filterMap_eq_filterMap! (h := h.balanced)]
  exact h.filterMap

/-!
### filter!
-/

theorem filter_eq_filter! [Ord α] {t : Impl α β} {h} {f : (a : α) → β a → Bool} :
    (t.filter f h).impl = t.filter! f := by
  induction t with
  | leaf => rfl
  | inner sz k v l r ihl ihr =>
    simp only [filter!, filter]
    split
    · simp only [ihl, ihr, link2_eq_link2!, h.left, h.right]
    · simp only [ihl, ihr, link_eq_link!, h.left, h.right]

theorem WF.filter! {_ : Ord α} {t : Impl α β} {f : (a : α) → β a → Bool} (h : t.WF) :
    (t.filter! f).WF := by
  rw [← filter_eq_filter! (h := h.balanced)]
  exact h.filter

/-!
### map
-/

theorem toListModel_map [Ord α] {t : Impl α β} {f : (a : α) → β a → γ a} :
    (t.map f).toListModel = t.toListModel.map fun x => ⟨x.1, f x.1 x.2⟩ := by
  induction t
  · next ihl ihr =>
    simp [map, ihl, ihr]
  · rfl

theorem sameKeys_map [Ord α] {t : Impl α β} {f : (a : α) → β a → γ a} : SameKeys (t.map f) t := by
  induction t with
  | leaf => exact .leaf
  | inner => apply SameKeys.inner <;> assumption

@[simp]
theorem size_map [Ord α] {t : Impl α β} {f : (a : α) → β a → γ a} : (t.map f).size = t.size :=
  sameKeys_map.size_eq

theorem WF.map [Ord α] {t : Impl α β} {f : (a : α) → β a → γ a} (h : t.WF) : (t.map f).WF :=
  sameKeys_map.symm.wf h

end Std.DTreeMap.Internal.Impl
