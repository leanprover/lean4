/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Std.Data.Iterators.Lemmas.Producers.Slice
public import Init.Data.Slice
public import Std.Data.DTreeMap.Internal.Lemmas

namespace Std.DTreeMap.Internal

namespace Impl

/--
  Removes all elements with key less than or equal to `lowerBound`.

  Does not modify size information stored in the tree.
-/
def pruneLE {α β} [Ord α] (t : Internal.Impl α β) (lowerBound : α) : Internal.Impl α β :=
  match t with
  | .leaf => .leaf
  | .inner sz k v l r =>
    match compare lowerBound k with
    | .lt => .inner sz k v (l.pruneLE lowerBound) r
    | .eq => .inner sz k v .leaf r
    | .gt => r.pruneLE lowerBound

/--
  Removes all elements with key less than to `lowerBound`.

  Does not modify size information stored in the tree.
-/
def pruneLT {α β} [Ord α] (t : Internal.Impl α β) (lowerBound : α) : Internal.Impl α β :=
  match t with
  | .leaf => .leaf
  | .inner sz k v l r =>
    match compare lowerBound k with
    | .lt => .inner sz k v (l.pruneLT lowerBound) r
    | .eq => r
    | .gt => r.pruneLT lowerBound

theorem toList_pruneLE {α β} [Ord α] [TransOrd α] (t : Internal.Impl α β) (ord_t : t.Ordered) (lowerBound : α) :
    (t.pruneLE lowerBound).toList = t.toList.filter (fun e => (compare e.fst lowerBound).isGE) := by
  induction t
  case leaf =>
    simp only [pruneLE, toList_eq_toListModel, toListModel_leaf, List.filter_nil]
  case inner _ k v l r l_ih r_ih =>
    simp only [pruneLE, toList_eq_toListModel, toListModel_inner, List.filter_append]
    generalize heq : compare lowerBound k = x
    cases x
    case lt =>
      simp only [toListModel_inner]
      specialize l_ih (Internal.Impl.Ordered.left ord_t)
      rw [toList_eq_toListModel] at l_ih
      simp only [l_ih, toList_eq_toListModel, List.filter, List.append_cancel_left_eq]
      rw [OrientedOrd.eq_swap, Ordering.swap_eq_lt] at heq
      simp only [heq, Ordering.isGE_gt, List.cons.injEq, true_and]
      symm
      apply List.filter_eq_self.2
      intro a mem
      apply Ordering.isGE_of_eq_gt
      apply TransCmp.gt_trans ?_ heq
      rw [OrientedOrd.eq_swap, Ordering.swap_eq_gt]
      exact Internal.Impl.Ordered.compare_right ord_t mem
    case eq =>
      simp only [toListModel_inner, toListModel_leaf, List.nil_append, List.filter]
      rw [OrientedCmp.eq_comm] at heq
      simp only [heq, Ordering.isGE_eq]
      suffices new_goal : List.filter (fun e => (compare e.fst lowerBound).isGE) l.toListModel = [] by
        simp only [new_goal, List.nil_append, List.cons.injEq, true_and]
        symm
        apply List.filter_eq_self.2
        intro a mem
        apply Ordering.isGE_of_eq_gt
        apply TransCmp.gt_of_gt_of_eq ?_ heq
        rw [OrientedOrd.eq_swap, Ordering.swap_eq_gt]
        apply Internal.Impl.Ordered.compare_right ord_t mem
      rw [List.filter_eq_nil_iff]
      intro a mem
      simp only [Bool.not_eq_true, Ordering.isGE_eq_false]
      exact TransCmp.lt_of_lt_of_eq (Internal.Impl.Ordered.compare_left ord_t mem) heq
    case gt =>
      simp only [List.filter]
      rw [OrientedOrd.eq_swap, Ordering.swap_eq_gt] at heq
      rw [heq]
      simp
      suffices new_goal : List.filter (fun e => (compare e.fst lowerBound).isGE) l.toListModel = [] by
        simp only [new_goal, List.nil_append]
        simp only [toList_eq_toListModel] at r_ih
        apply r_ih
        exact Internal.Impl.Ordered.right ord_t
      rw [List.filter_eq_nil_iff]
      intro a mem
      simp only [Bool.not_eq_true, Ordering.isGE_eq_false]
      exact TransCmp.lt_trans (Internal.Impl.Ordered.compare_left ord_t mem) heq

theorem toList_pruneLT {α β} [Ord α] [TransOrd α] (t : Internal.Impl α β) (ord_t : t.Ordered) (lowerBound : α) :
    (t.pruneLT lowerBound).toList = t.toList.filter (fun e => (compare e.fst lowerBound).isGT) := by
  induction t
  case leaf =>
    simp only [pruneLT, toList_eq_toListModel, toListModel_leaf, List.filter_nil]
  case inner _ k v l r l_ih r_ih =>
    simp only [pruneLT, toList_eq_toListModel, toListModel_inner, List.filter_append]
    generalize heq : compare lowerBound k = x
    cases x
    case lt =>
      simp
      specialize l_ih (Internal.Impl.Ordered.left ord_t)
      rw [toList_eq_toListModel] at l_ih
      simp only [l_ih, toList_eq_toListModel, List.filter, List.append_cancel_left_eq]
      rw [OrientedOrd.eq_swap, Ordering.swap_eq_lt] at heq
      simp only [heq, Ordering.isGT_gt, List.cons.injEq, true_and]
      symm
      apply List.filter_eq_self.2
      intro a mem
      rw [Ordering.isGT_iff_eq_gt]
      apply TransCmp.gt_trans ?_ heq
      rw [OrientedOrd.eq_swap, Ordering.swap_eq_gt]
      exact Internal.Impl.Ordered.compare_right ord_t mem
    case eq =>
      simp only [List.filter]
      rw [OrientedCmp.eq_comm] at heq
      rw [heq]
      suffices new_goal : List.filter (fun e => (compare e.fst lowerBound).isGT) l.toListModel = [] ∧
          List.filter (fun e => (compare e.fst lowerBound).isGT) r.toListModel = r.toListModel by
        simp only [new_goal, Ordering.isGT_eq, List.nil_append]
      apply And.intro
      · rw [List.filter_eq_nil_iff]
        intro a mem
        simp only [Ordering.isGT_iff_eq_gt, ← Ordering.isLE_iff_ne_gt]
        apply TransOrd.isLE_trans _ (Ordering.isLE_of_eq_eq heq)
        apply Ordering.isLE_of_eq_lt
        exact Internal.Impl.Ordered.compare_left ord_t mem
      · apply List.filter_eq_self.2
        intro a mem
        rw [Ordering.isGT_iff_eq_gt]
        apply TransCmp.gt_of_gt_of_eq ?_ heq
        rw [OrientedOrd.eq_swap, Ordering.swap_eq_gt]
        exact Internal.Impl.Ordered.compare_right ord_t mem
    case gt =>
      simp only [List.filter]
      rw [OrientedOrd.eq_swap] at heq
      rw [Ordering.swap_eq_gt] at heq
      simp only [heq, Ordering.isGT_lt]
      specialize r_ih (Ordered.right ord_t)
      rw [toList_eq_toListModel] at r_ih
      simp only [r_ih, toList_eq_toListModel, List.self_eq_append_left, List.filter_eq_nil_iff,
        Ordering.isGT_iff_eq_gt]
      intro a mem
      rw [← Ordering.isLE_iff_ne_gt]
      apply Ordering.isLE_of_eq_lt
      exact TransCmp.lt_trans (Internal.Impl.Ordered.compare_left ord_t mem) heq

end Impl

open Std.Iterators

section Zipper

public inductive Zipper (α : Type u) (β : α → Type v) where
  | done
  | cons (k : α) (v : β k) (tree : Impl α β) (next : Zipper α β)

variable {α : Type u} {β : α → Type v}

public def Zipper.toList : Zipper α β → List ((a : α) × β a)
| .done => []
| .cons k v tree next => ⟨k,v⟩ :: tree.toList ++ next.toList

public def Zipper.Ordered [Ord α] (t : Zipper α β) : Prop :=
  t.toList.Pairwise (fun a b => compare a.1 b.1 = .lt)

def Zipper.size : Zipper α β → Nat
| .done => 0
| .cons _ _ tree next => 1 + tree.treeSize + next.size

public def Zipper.prependMap : Impl α β → Zipper α β → Zipper α β
  | .leaf, it => it
  | .inner _ k v l r, it => prependMap l (.cons k v r it)

public def Zipper.prependMapGE [Ord α] (t : Impl α β) (lowerBound : α)
    (it : Zipper α β) : Zipper α β :=
  match t with
  | .leaf => it
  | .inner _ k v l r =>
    match compare lowerBound k with
    | .lt => prependMapGE l lowerBound (Zipper.cons k v r it)
    | .eq => .cons k v r it
    | .gt => prependMapGE r lowerBound it

public def Zipper.prependMapGT [Ord α] (t : Impl α β) (lowerBound : α)
    (it : Zipper α β) : Zipper α β :=
  match t with
  | .leaf => it
  | .inner _ k v l r =>
    match compare lowerBound k with
    | .lt => prependMapGT l lowerBound (Zipper.cons k v r it)
    | .eq => prependMapGT r lowerBound it
    | .gt => prependMapGT r lowerBound it

theorem Zipper.prependMap_pruneLE_eq_prependMapGE [Ord α] (t : Impl α β) (ord_t : t.Ordered)
    (z : Zipper α β) (lowerBound : α) :
    z.prependMap (t.pruneLE lowerBound) = z.prependMapGE t lowerBound := by
  induction t generalizing z
  case leaf =>
    simp only [Impl.pruneLE, Zipper.prependMap, Zipper.prependMapGE]
  case inner _ k v l r l_ih r_ih =>
    simp only [Impl.pruneLE, Zipper.prependMapGE]
    generalize heq : compare lowerBound k = x
    cases x
    case lt =>
      simp only
      apply l_ih
      exact Impl.Ordered.left ord_t
    case eq =>
      simp only [Zipper.prependMap]
    case gt =>
      simp only
      apply r_ih
      exact Impl.Ordered.right ord_t

theorem Zipper.prependMap_eq_prependMapGT_self [Ord α] [TransOrd α] (r : Impl α β)
    (z : Zipper α β) (lowerBound : α) (ord_r : r.Ordered)
    (hyp : ∀ e ∈ r.toList, compare lowerBound e.fst = .lt) :
    Zipper.prependMap r z = Zipper.prependMapGT r lowerBound z := by
  induction r generalizing z
  case leaf =>
    trivial
  case inner _ k v l r l_ih r_ih =>
    simp only [Zipper.prependMap, Zipper.prependMapGT]
    have hyp' := hyp ⟨k,v⟩ (by simp only [Impl.toList_eq_toListModel,
      Impl.toListModel_inner, List.mem_append, List.mem_cons, true_or, or_true])
    simp at hyp'
    rw [hyp']
    apply l_ih
    · exact (Impl.Ordered.left ord_r)
    · intro e mem
      apply hyp e
      simp only [Impl.toList_eq_toListModel, Impl.toListModel_inner,
        List.mem_append, List.mem_cons]
      apply Or.inl
      · rw [Impl.toList_eq_toListModel] at mem
        exact mem

theorem Zipper.prependMap_pruneLT_eq_prependMapGT [Ord α] [TransOrd α] (t : Impl α β)
    (ord_t : t.Ordered) (z : Zipper α β) (lowerBound : α) :
    z.prependMap (t.pruneLT lowerBound) = z.prependMapGT t lowerBound := by
  induction t generalizing z
  case leaf =>
    simp only [Impl.pruneLT, Zipper.prependMap, Zipper.prependMapGT]
  case inner _ k v l r l_ih r_ih =>
    simp only [Impl.pruneLT, Zipper.prependMapGT]
    generalize heq : compare lowerBound k = x
    cases x
    case lt =>
      simp only [Zipper.prependMap]
      apply l_ih
      exact Impl.Ordered.left ord_t
    case eq =>
      simp only
      apply Zipper.prependMap_eq_prependMapGT_self
      · exact Impl.Ordered.right ord_t
      · intro e mem
        apply TransCmp.lt_of_eq_of_lt heq
        apply Impl.Ordered.compare_right ord_t
        rw [← Impl.toList_eq_toListModel]
        exact mem
    case gt =>
      simp
      apply r_ih
      exact Impl.Ordered.right ord_t

theorem Zipper.toList_prependMap_eq_append (t : Impl α β)
    (it : Zipper α β) : (Zipper.prependMap t it).toList = t.toList ++ it.toList := by
  induction t generalizing it
  case leaf =>
    simp only [prependMap, Impl.toList_eq_toListModel, Impl.toListModel_leaf,
      List.nil_append]
  case inner _ k v l r l_ih r_ih =>
    simp only [Zipper.prependMap]
    specialize l_ih (Zipper.cons k v r it)
    rw [l_ih]
    simp only [Impl.toList_eq_toListModel, toList, List.cons_append,
      Impl.toListModel_inner, List.append_assoc]

theorem Zipper.toList_prependMap_done (t : Impl α β) : (Zipper.prependMap t .done).toList = t.toList := by
  simp [Zipper.toList_prependMap_eq_append, Zipper.toList]

theorem Zipper.ordered_prependMap [Ord α] [TransOrd α] {t : Impl α β}
    {ord_t : t.Ordered} {z : Zipper α β} {ord_z : z.Ordered}
    (hyp : ∀ k ∈ z.toList, ∀ k' ∈ t.toListModel, compare k'.1 k.1 = .lt) :
    (Zipper.prependMap t z).Ordered := by
  rw [Ordered, toList_prependMap_eq_append, List.pairwise_append]
  refine ⟨by rwa [Impl.toList_eq_toListModel], ord_z, ?_⟩
  exact fun a ha b hb => hyp _ hb _ (Impl.toList_eq_toListModel ▸ ha)

theorem Zipper.ordered_prependMap_done [Ord α] [TransOrd α] {t : Impl α β}
    {ord_t : t.Ordered} :
    (Zipper.prependMap t .done).Ordered := by
  apply ordered_prependMap
  · exact ord_t
  · simp only [Ordered, toList, List.Pairwise.nil]
  simp only [toList, List.not_mem_nil, false_implies, implies_true]

theorem Zipper.ordered_of_ordered_cons [Ord α] [TransOrd α] {t : Impl α β}
    {z : Zipper α β} : (Zipper.cons k v t z).Ordered → z.Ordered := by
  intro hyp
  simp only [Zipper.Ordered, Zipper.toList] at hyp
  simp only [Ordered]
  exact List.Pairwise.sublist (List.sublist_append_right (⟨k, v⟩ :: t.toList) z.toList) hyp

theorem Zipper.size_prependMap (t : Impl α β) (it : Zipper α β) :
    (Zipper.prependMap t it).size = t.treeSize + it.size := by
  fun_induction Zipper.prependMap
  case case1 =>
   simp only [Impl.treeSize, Nat.zero_add]
  case case2 size k v l r it ih =>
    simp only [ih, Zipper.size, Impl.treeSize, ← Nat.add_assoc, Nat.add_comm]

public def Zipper.step : Zipper α β → IterStep (IterM (α := Zipper α β) Id ((a : α) × β a)) ((a : α) × β a)
  | .done => .done
  | .cons k v t it =>
    .yield ⟨it.prependMap t⟩ ⟨k, v⟩

public instance : Iterator (Zipper α β) Id ((a : α) × β a) where
  IsPlausibleStep it step := it.internalState.step = step
  step it := ⟨it.internalState.step, rfl⟩

public instance : IteratorCollect (Zipper α β) Id Id := .defaultImplementation


def Zipper.FinitenessRelation : FinitenessRelation (Zipper α β) Id where
  rel t' t := t'.internalState.size < t.internalState.size
  wf := by
    apply InvImage.wf
    exact Nat.lt_wfRel.wf
  subrelation {it it'} h := by
    obtain ⟨w, h, h'⟩ := h
    simp only [IterM.IsPlausibleStep, Iterator.IsPlausibleStep] at h'
    cases w
    case skip it'' =>
      cases h
      simp only [Zipper.step] at h'
      split at h'
      any_goals contradiction
    case done =>
      cases h
    case yield it'' out =>
      cases h
      simp only [step] at h'
      split at h'
      case h_1 =>
        contradiction
      case h_2 h2 =>
          simp at h'
          simp only [h2, ← h'.1, Zipper.size_prependMap, Zipper.size, Nat.add_lt_add_iff_right,
            Nat.lt_add_left_iff_pos, Nat.lt_add_one]

@[no_expose]
public instance Zipper.instFinite : Finite (Zipper α β) Id :=
  .of_finitenessRelation Zipper.FinitenessRelation

public def Zipper.iter (t : Zipper α β) : Iter (α := Zipper α β) ((a : α) × β a) := ⟨t⟩

public def Zipper.iterOfTree (t : Impl α β) : Iter (α := Zipper α β) ((a : α) × β a) :=
  Zipper.iter <| Zipper.done.prependMap t

public instance {z : Zipper α β} : ToIterator z Id ((a : α) × β a) where
  State := Zipper α β
  iterMInternal := Iter.toIterM <| Zipper.iter z

@[simp]
theorem Zipper.toList_done : (done : Zipper α β).toList = [] := rfl

@[simp]
theorem Zipper.toList_cons : (cons k v tree next).toList = ⟨k, v⟩ :: tree.toList ++ next.toList := rfl

@[simp]
theorem Zipper.step_done : (done : Zipper α β).step = .done := rfl

@[simp]
theorem Zipper.step_cons : (cons k v t it : Zipper α β).step = .yield ⟨it.prependMap t⟩ ⟨k, v⟩ := rfl

@[simp]
theorem Zipper.val_run_step_toIterM_iter {z : Zipper α β} : z.iter.toIterM.step.run.val = z.step := rfl

theorem Zipper.eq_toIterM_iter (it : IterM (α := Zipper α β) Id ((a : α) × β a)) :
    it = it.internalState.iter.toIterM := rfl

@[simp]
theorem Zipper.size_cons : (cons k v t it : Zipper α β).size = 1 + t.treeSize + it.size := rfl

theorem Zipper.toList_iter {α β} {z : Zipper α β} : z.iter.toList = z.toList := by
  rw [Iter.toList_eq_toList_toIterM, IterM.toList_eq_match_step]
  simp only [bind_pure_comp, Id.run_bind, val_run_step_toIterM_iter]
  cases z with
  | done => simp
  | cons k v t it' =>
    simp only [step_cons, Id.run_map, toList_cons, List.cons_append, List.cons.injEq, true_and]
    rw [eq_toIterM_iter ⟨prependMap _ _⟩]
    simp only
    rw [← Iter.toList_eq_toList_toIterM, toList_iter, toList_prependMap_eq_append]
termination_by z.size
decreasing_by simp [size_prependMap]

public theorem Zipper.toList_iterOfTree (t : Impl α β) :
    (Zipper.iterOfTree t).toList = t.toList := by
  rw [Zipper.iterOfTree, Zipper.iter]
  have := @Zipper.toList_iter α β (prependMap t .done)
  simp only [iter] at this
  rw [this]
  simp only [Zipper.toList_prependMap_eq_append, toList, List.append_nil]

end Zipper

section Rxc

public structure RxcIterator (α : Type u) (β : α → Type v) [Ord α] where
  iter : Zipper α β
  upper : α

variable {α : Type u} {β : α → Type v}

public def RxcIterator.step [Ord α] : RxcIterator α β → IterStep (IterM (α := RxcIterator α β) Id ((a : α) × β a)) ((a : α) × β a)
  | ⟨.done, _⟩ => .done
  | ⟨.cons k v t it, upper⟩ =>
    if (compare k upper).isLE then
      .yield ⟨it.prependMap t, upper⟩ ⟨k, v⟩
    else
      .done

public instance [Ord α] : Iterator (RxcIterator α β) Id ((a : α) × β a) where
  IsPlausibleStep it step := it.internalState.step = step
  step it := ⟨it.internalState.step, rfl⟩

public instance [Ord α] : IteratorCollect (RxcIterator α β) Id Id := .defaultImplementation

def RxcIterator.FinitenessRelation [Ord α] : FinitenessRelation (RxcIterator α β) Id where
  rel t' t := t'.internalState.iter.size < t.internalState.iter.size
  wf := by
    apply InvImage.wf
    exact Nat.lt_wfRel.wf
  subrelation {it it'} h := by
    obtain ⟨w, h, h'⟩ := h
    simp only [IterM.IsPlausibleStep, Iterator.IsPlausibleStep] at h'
    cases w
    case skip it'' =>
      cases h
      simp only [RxcIterator.step] at h'
      split at h'
      any_goals contradiction
      · split at h'
        all_goals contradiction
    case done =>
      cases h
    case yield it'' out =>
      cases h
      simp only [RxcIterator.step] at h'
      split at h'
      case h_1 =>
        contradiction
      case h_2 h2 =>
        split at h'
        case isFalse =>
          contradiction
        case isTrue heq =>
          simp at h'
          simp only [h2, ← h'.1, Zipper.size_prependMap, Zipper.size, Nat.add_lt_add_iff_right,
            Nat.lt_add_left_iff_pos, Nat.lt_add_one]

@[no_expose]
public instance instFinite [Ord α] : Finite (RxcIterator α β) Id :=
  .of_finitenessRelation RxcIterator.FinitenessRelation

@[simp]
theorem RxcIterator.step_done [Ord α] {upper : α} : ({ iter := .done, upper := upper } : RxcIterator α β).step = .done := rfl

@[simp]
theorem RxcIterator.step_cons_of_LE [Ord α] {upper : α} {h : (compare k upper).isLE} : ({ iter := (.cons k v t it), upper := upper } : RxcIterator α β).step = .yield ⟨it.prependMap t, upper⟩ ⟨k,v⟩ := by
  rw [step, h]
  simp only [↓reduceIte]

@[simp]
theorem RxcIterator.step_cons_of_not_LE [Ord α] {upper : α} {h : (compare k upper).isLE = false} : ({ iter := (.cons k v t it), upper := upper } : RxcIterator α β).step = .done := by
  rw [step, h]
  simp only [Bool.false_eq_true, ↓reduceIte]

@[simp]
theorem RxcIterator.val_run_step_toIterM_iter [Ord α] {z : RxcIterator α β} : (⟨z⟩ : Iter (α := RxcIterator α β) ((a : α) × β a)).toIterM.step.run.val = z.step := rfl

theorem RxcIterator.eq_toIterM_iter [Ord α] (it : Iter (α := RxcIterator α β) ((a : α) × β a)) :
    it.toIterM = ⟨it.internalState⟩ := by rfl

theorem RxcIterator.toList_rxcIter {α β} [Ord α]
    {z : Zipper α β} {bound : α} :
    (⟨RxcIterator.mk z bound⟩ : Iter (Sigma β)).toList =
      z.toList.takeWhile (fun e => (compare e.fst bound).isLE) := by
  rw [Iter.toList_eq_toList_toIterM, IterM.toList_eq_match_step]
  simp only [bind_pure_comp, Id.run_bind]
  rw [val_run_step_toIterM_iter]
  cases z with
  | done => simp
  | cons k v t it' =>
    generalize heq : (compare k bound).isLE = x
    cases x
    · simp only [@RxcIterator.step_cons_of_not_LE _ _ k v t it' _ bound heq, Id.run_pure,
      Zipper.toList_cons, List.cons_append, heq, Bool.false_eq_true, not_false_eq_true,
      List.takeWhile_cons_of_neg]
    · simp only [@RxcIterator.step_cons_of_LE _ _ k v t it' _ bound heq, Id.run_map,
      Zipper.toList_cons, List.cons_append, heq, List.takeWhile_cons_of_pos, List.cons.injEq,
      true_and]
      rw [← eq_toIterM_iter, ← Iter.toList_eq_toList_toIterM, toList_rxcIter, Zipper.toList_prependMap_eq_append]
termination_by z.size
decreasing_by
  simp_all [Zipper.size_prependMap]

theorem toList_eq_takeWhile_list {α : Type u} {β : α → Type v} [Ord α] [TransOrd α] {bound : α} {l : List ((a : α) × β a)}
    {l_ordered : l.Pairwise (fun a b => compare a.1 b.1 = .lt)} :
  l.takeWhile (fun e => (compare e.fst bound).isLE) = l.filter (fun e => (compare e.fst bound).isLE) := by
    induction l
    case nil =>
      simp
    case cons h t t_ih =>
      simp only [List.takeWhile, List.filter]
      generalize heq : (compare h.fst bound).isLE = x
      cases x
      case true =>
        simp
        apply t_ih
        simp at l_ordered
        exact l_ordered.2
      case false =>
        simp_all
        intro a mem
        have := l_ordered.1 a mem
        rw [← Ordering.swap_eq_gt] at this
        apply TransCmp.gt_of_gt_of_gt
        · rw [← OrientedOrd.eq_swap] at this
          · exact this
        · exact heq

public theorem toList_eq_takeWhile {α β} [Ord α] [TransOrd α] {z : Zipper α β} {bound : α} {z_ord : z.Ordered} :
    z.toList.takeWhile (fun e => (compare e.fst bound).isLE) = z.toList.filter (fun e => (compare e.fst bound).isLE) := by
  simp only [Zipper.Ordered] at z_ord
  apply toList_eq_takeWhile_list
  exact z_ord

end Rxc

section Rxo

public structure RxoIterator (α : Type u) (β : α → Type v) [Ord α] where
  iter : Zipper α β
  upper : α

variable {α : Type u} {β : α → Type v}

public def RxoIterator.step [Ord α] : RxoIterator α β → IterStep (IterM (α := RxoIterator α β) Id ((a : α) × β a)) ((a : α) × β a)
  | ⟨.done, _⟩ => .done
  | ⟨.cons k v t it, upper⟩ =>
    if (compare k upper).isLT then
      .yield ⟨it.prependMap t, upper⟩ ⟨k, v⟩
    else
      .done

public instance [Ord α] : Iterator (RxoIterator α β) Id ((a : α) × β a) where
  IsPlausibleStep it step := it.internalState.step = step
  step it := ⟨it.internalState.step, rfl⟩

public instance [Ord α] : IteratorCollect (RxoIterator α β) Id Id := .defaultImplementation

def RxoIterator.instFinitenessRelation [Ord α] : FinitenessRelation (RxoIterator α β) Id where
  rel t' t := t'.internalState.iter.size < t.internalState.iter.size
  wf := by
    apply InvImage.wf
    exact Nat.lt_wfRel.wf
  subrelation {it it'} h := by
    obtain ⟨w, h, h'⟩ := h
    simp only [IterM.IsPlausibleStep, Iterator.IsPlausibleStep] at h'
    cases w
    case skip it'' =>
      cases h
      simp only [RxoIterator.step] at h'
      split at h'
      any_goals contradiction
      · split at h'
        all_goals contradiction
    case done =>
      cases h
    case yield it'' out =>
      cases h
      simp only [RxoIterator.step] at h'
      split at h'
      case h_1 =>
        contradiction
      case h_2 h2 =>
        split at h'
        case isFalse =>
          contradiction
        case isTrue heq =>
          simp at h'
          simp only [h2, ← h'.1, Zipper.size_prependMap, Zipper.size, Nat.add_lt_add_iff_right,
            Nat.lt_add_left_iff_pos, Nat.lt_add_one]

@[no_expose]
public instance Rxo.instFinite [Ord α] : Finite (RxoIterator α β) Id :=
  .of_finitenessRelation RxoIterator.instFinitenessRelation

@[simp]
theorem RxoIterator.step_done [Ord α] {upper : α} : ({ iter := .done, upper := upper } : RxoIterator α β).step = .done := rfl

@[simp]
theorem RxoIterator.step_cons_of_isLT [Ord α] {upper : α} {h : (compare k upper).isLT} : ({ iter := (.cons k v t it), upper := upper } : RxoIterator α β).step = .yield ⟨it.prependMap t, upper⟩ ⟨k,v⟩ := by
  rw [step, h]
  simp only [↓reduceIte]

@[simp]
theorem RxoIterator.step_cons_of_isLT_eq_false [Ord α] {upper : α} {h : (compare k upper).isLT = false} : ({ iter := (.cons k v t it), upper := upper } : RxoIterator α β).step = .done := by
  rw [step, h]
  simp only [Bool.false_eq_true, ↓reduceIte]

@[simp]
theorem RxoIterator.val_run_step_toIterM_iter [Ord α] {z : RxoIterator α β} : (⟨z⟩ : Iter (α := RxoIterator α β) ((a : α) × β a)).toIterM.step.run.val = z.step := rfl

theorem RxoIterator.eq_toIterM_iter [Ord α] (it : Iter (α := RxoIterator α β) ((a : α) × β a)) :
    it.toIterM = ⟨it.internalState⟩ := by rfl

theorem RxoIterator.toList_rxoIter {α β} [Ord α]
    {z : Zipper α β} {bound : α} :
    (⟨RxoIterator.mk z bound⟩ : Iter (Sigma β)).toList =
      z.toList.takeWhile (fun e => (compare e.fst bound).isLT) := by
  rw [Iter.toList_eq_toList_toIterM, IterM.toList_eq_match_step]
  simp only [bind_pure_comp, Id.run_bind]
  rw [val_run_step_toIterM_iter]
  cases z with
  | done => simp
  | cons k v t it' =>
    generalize heq : (compare k bound).isLT = x
    cases x
    · simp only [@RxoIterator.step_cons_of_isLT_eq_false _ _ k v t it' _ bound heq, Id.run_pure,
      Zipper.toList_cons, List.cons_append, heq, Bool.false_eq_true, not_false_eq_true,
      List.takeWhile_cons_of_neg]
    · simp only [@RxoIterator.step_cons_of_isLT _ _ k v t it' _ bound heq, Id.run_map,
      Zipper.toList_cons, List.cons_append, heq, List.takeWhile_cons_of_pos, List.cons.injEq,
      true_and]
      rw [← eq_toIterM_iter, ← Iter.toList_eq_toList_toIterM, toList_rxoIter, Zipper.toList_prependMap_eq_append]
termination_by z.size
decreasing_by
  simp_all [Zipper.size_prependMap]

theorem toList_eq_takeWhile_list_LT {α : Type u} {β : α → Type v} [Ord α] [TransOrd α] {bound : α} {l : List ((a : α) × β a)}
    {l_ordered : l.Pairwise (fun a b => compare a.1 b.1 = .lt)} :
  l.takeWhile (fun e => (compare e.fst bound).isLT) = l.filter (fun e => (compare e.fst bound).isLT) := by
    induction l
    case nil =>
      simp
    case cons h t t_ih =>
      simp only [List.takeWhile, List.filter]
      generalize heq : (compare h.fst bound).isLT = x
      cases x
      case true =>
        simp
        apply t_ih
        simp at l_ordered
        exact l_ordered.2
      case false =>
        simp_all
        intro a mem
        have := l_ordered.1 a mem
        rw [← Ordering.swap_eq_gt, ← OrientedOrd.eq_swap] at this
        rw [Ordering.ne_lt_iff_isGE]
        simp only [Bool.eq_false_iff, ne_eq, Ordering.isLT_iff_eq_lt] at heq
        rw [Ordering.ne_lt_iff_isGE] at heq
        apply TransOrd.isGE_trans
        · apply Ordering.isGE_of_eq_gt this
        · exact heq

public theorem toList_eq_takeWhile_LT {α β} [Ord α] [TransOrd α] {z : Zipper α β} {bound : α} {z_ord : z.Ordered} :
    z.toList.takeWhile (fun e => (compare e.fst bound).isLT) = z.toList.filter (fun e => (compare e.fst bound).isLT) := by
  simp only [Zipper.Ordered] at z_ord
  apply toList_eq_takeWhile_list_LT
  exact z_ord

end Rxo

section Ric

public structure RicSliceData (α : Type u) (β : α → Type v) [Ord α] where
  treeMap : Impl α β
  range : Ric α

public abbrev RicSlice α β [Ord α] := Slice (RicSliceData α β)

public instance {α : Type u} {β : α → Type v} [Ord α] : Ric.Sliceable (Impl α β) α (RicSlice α β) where
  mkSlice carrier range := ⟨carrier, range⟩

public instance [Ord α] {s : RicSlice α β} : ToIterator s Id ((a : α) × β a) :=
  ToIterator.of (RxcIterator α β) ⟨RxcIterator.mk (Zipper.prependMap s.1.treeMap Zipper.done) s.1.range.upper⟩

public theorem toList_ric {α : Type u} {β : α → Type v} [Ord α] [TransOrd α] (t : Impl α β)
    (ordered : t.Ordered) (bound : α) : t[*...=bound].toList = t.toList.filter (fun e => (compare e.fst bound).isLE) := by
  simp only [Ric.Sliceable.mkSlice, Slice.toList_eq_toList_iter, Slice.iter,
    Slice.Internal.iter_eq_toIteratorIter, ToIterator.iter, ToIterator.iterM_eq,
    Iter.toIter_toIterM]
  rw [RxcIterator.toList_rxcIter, toList_eq_takeWhile_list]
  · rw [Zipper.toList_prependMap_eq_append]
    simp [Zipper.toList]
  · apply Zipper.ordered_prependMap_done
    · exact ordered

end Ric

namespace Unit

public structure RicSliceData (α : Type u) [Ord α] where
  treeMap : Impl α (fun _ => Unit)
  range : Ric α

public abbrev RicSlice α [Ord α] := Slice (RicSliceData α)

public instance {α : Type u} [Ord α] : Ric.Sliceable (Impl α (fun _ => Unit)) α (Unit.RicSlice α) where
  mkSlice carrier range := ⟨carrier, range⟩

public instance [Ord α] {s : Unit.RicSlice α} : ToIterator s Id α := by
  apply ToIterator.of
  · exact (⟨RxcIterator.mk (Zipper.prependMap s.1.treeMap Zipper.done) s.1.range.upper⟩ : Iter _ ).map fun e => (e.1)

public theorem toList_ric {α : Type u} [Ord α] [TransOrd α] (t : Impl α (fun _ => Unit))
    (ordered : t.Ordered) (bound : α) : (t : Impl α (fun _ => Unit))[*...=bound].toList = (Internal.Impl.keys t).filter (fun e => (compare e bound).isLE) := by
  simp only [Ric.Sliceable.mkSlice, Slice.toList_eq_toList_iter, Slice.iter,
    Slice.Internal.iter_eq_toIteratorIter, ToIterator.iter, ToIterator.iterM_eq,
    Iter.toIter_toIterM]
  rw [Iter.toList_map]
  rw [← Std.DTreeMap.Internal.Impl.map_fst_toList_eq_keys]
  rw [List.filter_map]
  congr
  rw [RxcIterator.toList_rxcIter, toList_eq_takeWhile_list]
  · congr
    simp [Zipper.toList_prependMap_eq_append, Zipper.toList, Impl.toList_eq_toListModel]
  · apply Zipper.ordered_prependMap_done
    · exact ordered

end Unit

namespace Const

public structure RicSliceData (α : Type u) (β : Type v) [Ord α] where
  treeMap : Impl α (fun _ => β)
  range : Ric α

public abbrev RicSlice α β [Ord α] := Slice (RicSliceData α β)

public instance {α : Type u} {β : Type v} [Ord α] : Ric.Sliceable (Impl α (fun _ => β)) α (RicSlice α β) where
  mkSlice carrier range := ⟨carrier, range⟩

public instance [Ord α] {s : RicSlice α β} : ToIterator s Id (α × β) := by
  apply ToIterator.of
  · exact (⟨RxcIterator.mk (Zipper.prependMap s.1.treeMap Zipper.done) s.1.range.upper⟩ : Iter ((_ : α) × β)).map fun e => (e.1, e.2)

public theorem toList_ric {α : Type u} {β : Type v} [Ord α] [TransOrd α] (t : Impl α (fun _ => β))
    (ordered : t.Ordered) (bound : α) : t[*...=bound].toList = (Internal.Impl.Const.toList t).filter (fun e => (compare e.fst bound).isLE) := by
  simp only [Ric.Sliceable.mkSlice, Slice.toList_eq_toList_iter, Slice.iter,
    Slice.Internal.iter_eq_toIteratorIter, ToIterator.iter, ToIterator.iterM_eq,
    Iter.toIter_toIterM]
  rw [Iter.toList_map]
  rw [Impl.Const.toList_eq_toListModel_map]
  rw [List.filter_map]
  congr
  rw [RxcIterator.toList_rxcIter, toList_eq_takeWhile_list]
  · congr
    simp [Zipper.toList_prependMap_eq_append, Zipper.toList, Impl.toList_eq_toListModel]
  · apply Zipper.ordered_prependMap_done
    · exact ordered

end Const

section Rio

public structure RioSliceData (α : Type u) (β : α → Type v) [Ord α] where
  treeMap : Impl α β
  range : Rio α

public abbrev RioSlice α β [Ord α] := Slice (RioSliceData α β)

public instance {α : Type u} {β : α → Type v} [Ord α] : Rio.Sliceable (Impl α β) α (RioSlice α β) where
  mkSlice carrier range := ⟨carrier, range⟩

public instance [Ord α] {s : RioSlice α β} : ToIterator s Id ((a : α) × β a) :=
  ToIterator.of (RxoIterator α β) ⟨RxoIterator.mk (Zipper.prependMap s.1.treeMap Zipper.done) s.1.range.upper⟩

public theorem toList_rio {α : Type u} {β : α → Type v} [Ord α] [TransOrd α] (t : Impl α β)
    (ordered : t.Ordered) (bound : α) : t[*...bound].toList = t.toList.filter (fun e => (compare e.fst bound).isLT) := by
  simp only [Rio.Sliceable.mkSlice, Slice.toList_eq_toList_iter, Slice.iter,
    Slice.Internal.iter_eq_toIteratorIter, ToIterator.iter, ToIterator.iterM_eq,
    Iter.toIter_toIterM]
  rw [RxoIterator.toList_rxoIter, toList_eq_takeWhile_list_LT]
  · rw [Zipper.toList_prependMap_eq_append]
    simp [Zipper.toList]
  · apply Zipper.ordered_prependMap_done
    · exact ordered

end Rio

namespace Unit

public structure RioSliceData (α : Type u) [Ord α] where
  treeMap : Impl α (fun _ => Unit)
  range : Rio α

public abbrev RioSlice α [Ord α] := Slice (RioSliceData α)

public instance {α : Type u} [Ord α] : Rio.Sliceable (Impl α (fun _ => Unit)) α (Unit.RioSlice α) where
  mkSlice carrier range := ⟨carrier, range⟩

public instance [Ord α] {s : Unit.RioSlice α} : ToIterator s Id α := by
  apply ToIterator.of
  · exact (⟨RxoIterator.mk (Zipper.prependMap s.1.treeMap Zipper.done) s.1.range.upper⟩ : Iter _ ).map fun e => (e.1)

public theorem toList_rio {α : Type u} [Ord α] [TransOrd α] (t : Impl α (fun _ => Unit))
    (ordered : t.Ordered) (bound : α) : (t : Impl α (fun _ => Unit))[*...<bound].toList = (Internal.Impl.keys t).filter (fun e => (compare e bound).isLT) := by
  simp only [Rio.Sliceable.mkSlice, Slice.toList_eq_toList_iter, Slice.iter,
    Slice.Internal.iter_eq_toIteratorIter, ToIterator.iter, ToIterator.iterM_eq,
    Iter.toIter_toIterM]
  rw [Iter.toList_map]
  rw [← Std.DTreeMap.Internal.Impl.map_fst_toList_eq_keys]
  rw [List.filter_map]
  congr
  rw [RxoIterator.toList_rxoIter, toList_eq_takeWhile_list_LT]
  · congr
    simp [Zipper.toList_prependMap_eq_append, Zipper.toList, Impl.toList_eq_toListModel]
  · apply Zipper.ordered_prependMap_done
    · exact ordered

end Unit

namespace Const

public structure RioSliceData (α : Type u) (β : Type v) [Ord α] where
  treeMap : Impl α (fun _ => β)
  range : Rio α

public abbrev RioSlice α β [Ord α] := Slice (RioSliceData α β)

public instance {α : Type u} {β : Type v} [Ord α] : Rio.Sliceable (Impl α (fun _ => β)) α (RioSlice α β) where
  mkSlice carrier range := ⟨carrier, range⟩

public instance [Ord α] {s : RioSlice α β} : ToIterator s Id (α × β) := by
  apply ToIterator.of
  · exact (⟨RxoIterator.mk (Zipper.prependMap s.1.treeMap Zipper.done) s.1.range.upper⟩ : Iter ((_ : α) × β)).map fun e => (e.1, e.2)

public theorem toList_rio {α : Type u} {β : Type v} [Ord α] [TransOrd α] (t : Impl α (fun _ => β))
    (ordered : t.Ordered) (bound : α) : t[*...<bound].toList = (Internal.Impl.Const.toList t).filter (fun e => (compare e.fst bound).isLT) := by
  simp only [Rio.Sliceable.mkSlice, Slice.toList_eq_toList_iter, Slice.iter,
    Slice.Internal.iter_eq_toIteratorIter, ToIterator.iter, ToIterator.iterM_eq,
    Iter.toIter_toIterM]
  rw [Iter.toList_map]
  rw [Impl.Const.toList_eq_toListModel_map]
  rw [List.filter_map]
  congr
  rw [RxoIterator.toList_rxoIter, toList_eq_takeWhile_list_LT]
  · congr
    simp [Zipper.toList_prependMap_eq_append, Zipper.toList, Impl.toList_eq_toListModel]
  · apply Zipper.ordered_prependMap_done
    · exact ordered

end Const

section Rcc

@[always_inline]
public def RccIterator [Ord α] (t : Impl α β) (lowerBound : α) (upperBound : α)  : Iter (α := RxcIterator α β) ((a : α) × β a) :=
  ⟨RxcIterator.mk (Zipper.prependMapGE t lowerBound .done) upperBound⟩

theorem toList_rccIter {α β} [Ord α] [TransOrd α]
    {t : Impl α β} {t_ord : t.Ordered} {lowerBound upperBound : α} :
    (RccIterator t lowerBound upperBound : Iter (Sigma β)).toList =
      t.toList.filter (fun e => (compare e.fst lowerBound).isGE ∧ (compare e.fst upperBound).isLE) := by
  simp only [RccIterator, Bool.decide_and, Bool.decide_eq_true]
  rw [RxcIterator.toList_rxcIter, toList_eq_takeWhile_list]
  · conv =>
      rhs
      lhs
      ext x
      rw [Bool.and_comm]
    rw [← List.filter_filter]
    congr 1
    rw [← Zipper.prependMap_pruneLE_eq_prependMapGE]
    · rw [Zipper.toList_prependMap_eq_append]
      rw [Impl.toList_pruneLE]
      · simp [Zipper.toList]
      · exact t_ord
    · exact t_ord
  · rw [← Zipper.prependMap_pruneLE_eq_prependMapGE]
    · simp only [Zipper.toList_prependMap_eq_append, Zipper.toList, List.append_nil]
      rw [Impl.toList_pruneLE]
      · apply List.Pairwise.filter
        simp only [Impl.Ordered] at t_ord
        rw [Impl.toList_eq_toListModel]
        exact t_ord
      · exact t_ord
    · exact t_ord

public structure RccSliceData (α : Type u) (β : α → Type v) [Ord α] where
  treeMap : Impl α β
  range : Rcc α

public abbrev RccSlice α β [Ord α] := Slice (RccSliceData α β)

public instance {α : Type u} {β : α → Type v} [Ord α] : Rcc.Sliceable (Impl α β) α (RccSlice α β) where
  mkSlice carrier range := ⟨carrier, range⟩

public instance [Ord α] {s : RccSlice α β} : ToIterator s Id ((a : α) × β a) :=
  ToIterator.of (RxcIterator α β) (RccIterator s.1.treeMap s.1.range.lower s.1.range.upper)

public theorem toList_rcc {α : Type u} {β : α → Type v} [Ord α] [TransOrd α] (t : Impl α β)
    (ordered : t.Ordered) (lowerBound upperBound : α) : t[lowerBound...=upperBound].toList = t.toList.filter (fun e => (compare e.fst lowerBound).isGE ∧ (compare e.fst upperBound).isLE) := by
  simp only [Rcc.Sliceable.mkSlice, Slice.toList_eq_toList_iter, Slice.iter,
    Slice.Internal.iter_eq_toIteratorIter, ToIterator.iter, ToIterator.iterM_eq,
    Iter.toIter_toIterM]
  rw [toList_rccIter]
  · exact ordered

end Rcc

namespace Unit

public structure RccSliceData (α : Type u) [Ord α] where
  treeMap : Impl α (fun _ => Unit)
  range : Rcc α

public abbrev RccSlice α [Ord α] := Slice (RccSliceData α)

public instance {α : Type u} [Ord α] : Rcc.Sliceable (Impl α (fun _ => Unit)) α (Unit.RccSlice α) where
  mkSlice carrier range := ⟨carrier, range⟩

public instance [Ord α] {s : Unit.RccSlice α} : ToIterator s Id α := by
  apply ToIterator.of
  · exact (⟨RxcIterator.mk (Zipper.prependMapGE s.1.treeMap s.1.range.lower .done) s.1.range.upper⟩ : Iter _ ).map fun e => (e.1)

public theorem toList_rcc {α : Type u} [Ord α] [TransOrd α] (t : Impl α (fun _ => Unit))
    (ordered : t.Ordered) (lowerBound upperBound: α) : (t : Impl α (fun _ => Unit))[lowerBound...=upperBound].toList = (Internal.Impl.keys t).filter (fun e => (compare e lowerBound).isGE ∧ (compare e upperBound).isLE) := by
  simp only [Rcc.Sliceable.mkSlice, Slice.toList_eq_toList_iter, Slice.iter,
    Slice.Internal.iter_eq_toIteratorIter, ToIterator.iter, ToIterator.iterM_eq,
    Iter.toIter_toIterM]
  rw [Iter.toList_map]
  have := @toList_rccIter α (fun _ => Unit) _ _ t ordered lowerBound upperBound
  rw [RccIterator] at this
  rw [this]
  have eq : (fun (e : (_ : α) × Unit) => decide ((compare e.fst lowerBound).isGE = true ∧ (compare e.fst upperBound).isLE = true)) =
    (fun (e : α) => decide ((compare e lowerBound).isGE = true ∧ (compare e upperBound).isLE = true)) ∘ (fun e => e.fst) := by congr
  conv =>
    lhs
    rhs
    rw [eq]
  rw [← List.filter_map, ← Std.DTreeMap.Internal.Impl.map_fst_toList_eq_keys]

end Unit

namespace Const

public structure RccSliceData (α : Type u) (β : Type v) [Ord α] where
  treeMap : Impl α (fun _ => β)
  range : Rcc α

public abbrev RccSlice α β [Ord α] := Slice (RccSliceData α β)

public instance {α : Type u} {β : Type v} [Ord α] : Rcc.Sliceable (Impl α (fun _ => β)) α (RccSlice α β) where
  mkSlice carrier range := ⟨carrier, range⟩

public instance [Ord α] {s : RccSlice α β} : ToIterator s Id (α × β) := by
  apply ToIterator.of
  · exact (⟨RxcIterator.mk (Zipper.prependMapGE s.1.treeMap s.1.range.lower .done) s.1.range.upper⟩ : Iter ((_ : α) × β)).map fun e => (e.1, e.2)

public theorem toList_rcc {α : Type u} {β : Type v} [Ord α] [TransOrd α] (t : Impl α (fun _ => β))
    (ordered : t.Ordered) (lowerBound upperBound : α) : t[lowerBound...=upperBound].toList = (Internal.Impl.Const.toList t).filter (fun e => (compare e.fst lowerBound).isGE ∧ (compare e.fst upperBound).isLE) := by
  simp only [Rcc.Sliceable.mkSlice, Slice.toList_eq_toList_iter, Slice.iter,
    Slice.Internal.iter_eq_toIteratorIter, ToIterator.iter, ToIterator.iterM_eq,
    Iter.toIter_toIterM]
  rw [Iter.toList_map]
  have := @toList_rccIter α (fun _ => β) _ _ t ordered lowerBound upperBound
  rw [RccIterator] at this
  rw [this]
  have eq : (fun (e : (_ : α) × β) => decide ((compare e.fst lowerBound).isGE = true ∧ (compare e.fst upperBound).isLE = true)) =
    (fun (e : α × β) => decide ((compare e.fst lowerBound).isGE = true ∧ (compare e.fst upperBound).isLE = true)) ∘ (fun e => (e.1, e.2)) := by congr
  conv =>
    lhs
    rhs
    rw [eq]
  rw [← List.filter_map]
  congr
  rw [Impl.Const.toList_eq_toListModel_map, Impl.toList_eq_toListModel]

end Const

section Rco

@[always_inline]
public def RcoIterator [Ord α] (t : Impl α β) (lowerBound : α) (upperBound : α)  : Iter (α := RxoIterator α β) ((a : α) × β a) :=
  ⟨RxoIterator.mk (Zipper.prependMapGE t lowerBound .done) upperBound⟩

theorem toList_rcoIter {α β} [Ord α] [TransOrd α]
    {t : Impl α β} {t_ord : t.Ordered} {lowerBound upperBound : α} :
    (RcoIterator t lowerBound upperBound : Iter (Sigma β)).toList =
      t.toList.filter (fun e => (compare e.fst lowerBound).isGE ∧ (compare e.fst upperBound).isLT) := by
  simp only [RcoIterator, Bool.decide_and, Bool.decide_eq_true]
  rw [RxoIterator.toList_rxoIter, toList_eq_takeWhile_list_LT]
  · conv =>
      rhs
      lhs
      ext x
      rw [Bool.and_comm]
    rw [← List.filter_filter]
    congr 1
    rw [← Zipper.prependMap_pruneLE_eq_prependMapGE]
    · rw [Zipper.toList_prependMap_eq_append]
      rw [Impl.toList_pruneLE]
      · simp only [Zipper.toList, List.append_nil]
      · exact t_ord
    · exact t_ord
  · rw [← Zipper.prependMap_pruneLE_eq_prependMapGE]
    · simp only [Zipper.toList_prependMap_eq_append, Zipper.toList, List.append_nil]
      rw [Impl.toList_pruneLE]
      · apply List.Pairwise.filter
        simp only [Impl.Ordered] at t_ord
        rw [Impl.toList_eq_toListModel]
        exact t_ord
      · exact t_ord
    · exact t_ord

public structure RcoSliceData (α : Type u) (β : α → Type v) [Ord α] where
  treeMap : Impl α β
  range : Rco α

public abbrev RcoSlice α β [Ord α] := Slice (RcoSliceData α β)

public instance {α : Type u} {β : α → Type v} [Ord α] : Rco.Sliceable (Impl α β) α (RcoSlice α β) where
  mkSlice carrier range := ⟨carrier, range⟩

public instance [Ord α] {s : RcoSlice α β} : ToIterator s Id ((a : α) × β a) :=
  ToIterator.of (RxoIterator α β) (RcoIterator s.1.treeMap s.1.range.lower s.1.range.upper)

public theorem toList_rco {α : Type u} {β : α → Type v} [Ord α] [TransOrd α] (t : Impl α β)
    (ordered : t.Ordered) (lowerBound upperBound : α) : t[lowerBound...<upperBound].toList = t.toList.filter (fun e => (compare e.fst lowerBound).isGE ∧ (compare e.fst upperBound).isLT) := by
  simp only [Rco.Sliceable.mkSlice, Slice.toList_eq_toList_iter, Slice.iter,
    Slice.Internal.iter_eq_toIteratorIter, ToIterator.iter, ToIterator.iterM_eq,
    Iter.toIter_toIterM]
  rw [toList_rcoIter]
  · exact ordered

end Rco

namespace Unit

public structure RcoSliceData (α : Type u) [Ord α] where
  treeMap : Impl α (fun _ => Unit)
  range : Rco α

public abbrev RcoSlice α [Ord α] := Slice (RcoSliceData α)

public instance {α : Type u} [Ord α] : Rco.Sliceable (Impl α (fun _ => Unit)) α (Unit.RcoSlice α) where
  mkSlice carrier range := ⟨carrier, range⟩

public instance [Ord α] {s : Unit.RcoSlice α} : ToIterator s Id α := by
  apply ToIterator.of
  · exact (⟨RxoIterator.mk (Zipper.prependMapGE s.1.treeMap s.1.range.lower .done) s.1.range.upper⟩ : Iter _ ).map fun e => (e.1)

public theorem toList_rco {α : Type u} [Ord α] [TransOrd α] (t : Impl α (fun _ => Unit))
    (ordered : t.Ordered) (lowerBound upperBound: α) : (t : Impl α (fun _ => Unit))[lowerBound...<upperBound].toList = (Internal.Impl.keys t).filter (fun e => (compare e lowerBound).isGE ∧ (compare e upperBound).isLT) := by
  simp only [Rco.Sliceable.mkSlice, Slice.toList_eq_toList_iter, Slice.iter,
    Slice.Internal.iter_eq_toIteratorIter, ToIterator.iter, ToIterator.iterM_eq,
    Iter.toIter_toIterM]
  rw [Iter.toList_map]
  have := @toList_rcoIter α (fun _ => Unit) _ _ t ordered lowerBound upperBound
  rw [RcoIterator] at this
  rw [this]
  have eq : (fun (e : (_ : α) × Unit) => decide ((compare e.fst lowerBound).isGE = true ∧ (compare e.fst upperBound).isLT = true)) =
    (fun (e : α) => decide ((compare e lowerBound).isGE = true ∧ (compare e upperBound).isLT = true)) ∘ (fun e => e.fst) := by congr
  conv =>
    lhs
    rhs
    rw [eq]
  rw [← List.filter_map, ← Std.DTreeMap.Internal.Impl.map_fst_toList_eq_keys]

end Unit

namespace Const

public structure RcoSliceData (α : Type u) (β : Type v) [Ord α] where
  treeMap : Impl α (fun _ => β)
  range : Rco α

public abbrev RcoSlice α β [Ord α] := Slice (RcoSliceData α β)

public instance {α : Type u} {β : Type v} [Ord α] : Rco.Sliceable (Impl α (fun _ => β)) α (RcoSlice α β) where
  mkSlice carrier range := ⟨carrier, range⟩

public instance [Ord α] {s : RcoSlice α β} : ToIterator s Id (α × β) := by
  apply ToIterator.of
  · exact (⟨RxoIterator.mk (Zipper.prependMapGE s.1.treeMap s.1.range.lower .done) s.1.range.upper⟩ : Iter ((_ : α) × β)).map fun e => (e.1, e.2)

public theorem toList_rco {α : Type u} {β : Type v} [Ord α] [TransOrd α] (t : Impl α (fun _ => β))
    (ordered : t.Ordered) (lowerBound upperBound : α) : t[lowerBound...<upperBound].toList = (Internal.Impl.Const.toList t).filter (fun e => (compare e.fst lowerBound).isGE ∧ (compare e.fst upperBound).isLT) := by
  simp only [Rco.Sliceable.mkSlice, Slice.toList_eq_toList_iter, Slice.iter,
    Slice.Internal.iter_eq_toIteratorIter, ToIterator.iter, ToIterator.iterM_eq,
    Iter.toIter_toIterM]
  rw [Iter.toList_map]
  have := @toList_rcoIter α (fun _ => β) _ _ t ordered lowerBound upperBound
  rw [RcoIterator] at this
  rw [this]
  have eq : (fun (e : (_ : α) × β) => decide ((compare e.fst lowerBound).isGE = true ∧ (compare e.fst upperBound).isLT = true)) = (fun (e : α × β) => decide ((compare e.fst lowerBound).isGE = true ∧ (compare e.fst upperBound).isLT = true)) ∘ (fun e => (e.1, e.2)) := by congr
  conv =>
    lhs
    rhs
    rw [eq]
  rw [← List.filter_map]
  congr
  rw [Impl.Const.toList_eq_toListModel_map, Impl.toList_eq_toListModel]

end Const

section Roo

@[always_inline]
public def RooIterator [Ord α] (t : Impl α β) (lowerBound : α) (upperBound : α)  : Iter (α := RxoIterator α β) ((a : α) × β a) :=
  ⟨RxoIterator.mk (Zipper.prependMapGT t lowerBound .done) upperBound⟩

theorem toList_rooIter {α β} [Ord α] [TransOrd α]
    {t : Impl α β} {t_ord : t.Ordered} {lowerBound upperBound : α} :
    (RooIterator t lowerBound upperBound : Iter (Sigma β)).toList =
      t.toList.filter (fun e => (compare e.fst lowerBound).isGT ∧ (compare e.fst upperBound).isLT) := by
  simp only [RooIterator, Bool.decide_and, Bool.decide_eq_true]
  rw [RxoIterator.toList_rxoIter, toList_eq_takeWhile_list_LT]
  · conv =>
      rhs
      lhs
      ext x
      rw [Bool.and_comm]
    rw [← List.filter_filter]
    congr 1
    rw [← Zipper.prependMap_pruneLT_eq_prependMapGT]
    · rw [Zipper.toList_prependMap_eq_append]
      rw [Impl.toList_pruneLT]
      · simp only [Zipper.toList, List.append_nil]
      · exact t_ord
    · exact t_ord
  · rw [← Zipper.prependMap_pruneLT_eq_prependMapGT]
    · simp only [Zipper.toList_prependMap_eq_append, Zipper.toList, List.append_nil]
      rw [Impl.toList_pruneLT]
      · apply List.Pairwise.filter
        simp only [Impl.Ordered] at t_ord
        rw [Impl.toList_eq_toListModel]
        exact t_ord
      · exact t_ord
    · exact t_ord

public structure RooSliceData (α : Type u) (β : α → Type v) [Ord α] where
  treeMap : Impl α β
  range : Roo α

public abbrev RooSlice α β [Ord α] := Slice (RooSliceData α β)

public instance {α : Type u} {β : α → Type v} [Ord α] : Roo.Sliceable (Impl α β) α (RooSlice α β) where
  mkSlice carrier range := ⟨carrier, range⟩

public instance [Ord α] {s : RooSlice α β} : ToIterator s Id ((a : α) × β a) :=
  ToIterator.of (RxoIterator α β) (RooIterator s.1.treeMap s.1.range.lower s.1.range.upper)

public theorem toList_roo {α : Type u} {β : α → Type v} [Ord α] [TransOrd α] (t : Impl α β)
    (ordered : t.Ordered) (lowerBound upperBound : α) : t[lowerBound<...<upperBound].toList = t.toList.filter (fun e => (compare e.fst lowerBound).isGT ∧ (compare e.fst upperBound).isLT) := by
  simp only [Roo.Sliceable.mkSlice, Slice.toList_eq_toList_iter, Slice.iter,
    Slice.Internal.iter_eq_toIteratorIter, ToIterator.iter, ToIterator.iterM_eq,
    Iter.toIter_toIterM]
  rw [toList_rooIter]
  · exact ordered

end Roo

namespace Unit

public structure RooSliceData (α : Type u) [Ord α] where
  treeMap : Impl α (fun _ => Unit)
  range : Roo α

public abbrev RooSlice α [Ord α] := Slice (RooSliceData α)

public instance {α : Type u} [Ord α] : Roo.Sliceable (Impl α (fun _ => Unit)) α (Unit.RooSlice α) where
  mkSlice carrier range := ⟨carrier, range⟩

public instance [Ord α] {s : Unit.RooSlice α} : ToIterator s Id α := by
  apply ToIterator.of
  · exact (⟨RxoIterator.mk (Zipper.prependMapGT s.1.treeMap s.1.range.lower .done) s.1.range.upper⟩ : Iter _ ).map fun e => (e.1)

public theorem toList_roo {α : Type u} [Ord α] [TransOrd α] (t : Impl α (fun _ => Unit))
    (ordered : t.Ordered) (lowerBound upperBound: α) : (t : Impl α (fun _ => Unit))[lowerBound<...<upperBound].toList = (Internal.Impl.keys t).filter (fun e => (compare e lowerBound).isGT ∧ (compare e upperBound).isLT) := by
  simp only [Roo.Sliceable.mkSlice, Slice.toList_eq_toList_iter, Slice.iter,
    Slice.Internal.iter_eq_toIteratorIter, ToIterator.iter, ToIterator.iterM_eq,
    Iter.toIter_toIterM]
  rw [Iter.toList_map]
  have := @toList_rooIter α (fun _ => Unit) _ _ t ordered lowerBound upperBound
  rw [RooIterator] at this
  rw [this]
  have eq : (fun (e : (_ : α) × Unit) => decide ((compare e.fst lowerBound).isGT = true ∧ (compare e.fst upperBound).isLT = true)) =
    (fun (e : α) => decide ((compare e lowerBound).isGT = true ∧ (compare e upperBound).isLT = true)) ∘ (fun e => e.fst) := by congr
  conv =>
    lhs
    rhs
    rw [eq]
  rw [← List.filter_map, ← Std.DTreeMap.Internal.Impl.map_fst_toList_eq_keys]

end Unit

namespace Const

public structure RooSliceData (α : Type u) (β : Type v) [Ord α] where
  treeMap : Impl α (fun _ => β)
  range : Roo α

public abbrev RooSlice α β [Ord α] := Slice (RooSliceData α β)

public instance {α : Type u} {β : Type v} [Ord α] : Roo.Sliceable (Impl α (fun _ => β)) α (RooSlice α β) where
  mkSlice carrier range := ⟨carrier, range⟩

public instance [Ord α] {s : RooSlice α β} : ToIterator s Id (α × β) := by
  apply ToIterator.of
  · exact (⟨RxoIterator.mk (Zipper.prependMapGT s.1.treeMap s.1.range.lower .done) s.1.range.upper⟩ : Iter ((_ : α) × β)).map fun e => (e.1, e.2)

public theorem toList_roo {α : Type u} {β : Type v} [Ord α] [TransOrd α] (t : Impl α (fun _ => β))
    (ordered : t.Ordered) (lowerBound upperBound : α) : t[lowerBound<...<upperBound].toList = (Internal.Impl.Const.toList t).filter (fun e => (compare e.fst lowerBound).isGT ∧ (compare e.fst upperBound).isLT) := by
  simp only [Roo.Sliceable.mkSlice, Slice.toList_eq_toList_iter, Slice.iter,
    Slice.Internal.iter_eq_toIteratorIter, ToIterator.iter, ToIterator.iterM_eq,
    Iter.toIter_toIterM]
  rw [Iter.toList_map]
  have := @toList_rooIter α (fun _ => β) _ _ t ordered lowerBound upperBound
  rw [RooIterator] at this
  rw [this]
  have eq : (fun (e : (_ : α) × β) => decide ((compare e.fst lowerBound).isGT = true ∧ (compare e.fst upperBound).isLT = true)) =
    (fun (e : α × β) => decide ((compare e.fst lowerBound).isGT = true ∧ (compare e.fst upperBound).isLT = true)) ∘ (fun e => (e.1, e.2)) := by congr
  conv =>
    lhs
    rhs
    rw [eq]
  rw [← List.filter_map]
  congr
  rw [Impl.Const.toList_eq_toListModel_map, Impl.toList_eq_toListModel]

end Const

section Roc

@[always_inline]
public def RocIterator [Ord α] (t : Impl α β) (lowerBound : α) (upperBound : α)  : Iter (α := RxcIterator α β) ((a : α) × β a) :=
  ⟨RxcIterator.mk (Zipper.prependMapGT t lowerBound .done) upperBound⟩

theorem toList_rocIter {α β} [Ord α] [TransOrd α]
    {t : Impl α β} {t_ord : t.Ordered} {lowerBound upperBound : α} :
    (RocIterator t lowerBound upperBound : Iter (Sigma β)).toList =
      t.toList.filter (fun e => (compare e.fst lowerBound).isGT ∧ (compare e.fst upperBound).isLE) := by
  simp only [RocIterator, Bool.decide_and, Bool.decide_eq_true]
  rw [RxcIterator.toList_rxcIter, toList_eq_takeWhile_list]
  · conv =>
      rhs
      lhs
      ext x
      rw [Bool.and_comm]
    rw [← List.filter_filter]
    congr 1
    rw [← Zipper.prependMap_pruneLT_eq_prependMapGT]
    · rw [Zipper.toList_prependMap_eq_append]
      rw [Impl.toList_pruneLT]
      · simp only [Zipper.toList, List.append_nil]
      · exact t_ord
    · exact t_ord
  · rw [← Zipper.prependMap_pruneLT_eq_prependMapGT]
    · simp only [Zipper.toList_prependMap_eq_append, Zipper.toList, List.append_nil]
      rw [Impl.toList_pruneLT]
      · apply List.Pairwise.filter
        simp only [Impl.Ordered] at t_ord
        rw [Impl.toList_eq_toListModel]
        exact t_ord
      · exact t_ord
    · exact t_ord

public structure RocSliceData (α : Type u) (β : α → Type v) [Ord α] where
  treeMap : Impl α β
  range : Roc α

public abbrev RocSlice α β [Ord α] := Slice (RocSliceData α β)

public instance {α : Type u} {β : α → Type v} [Ord α] : Roc.Sliceable (Impl α β) α (RocSlice α β) where
  mkSlice carrier range := ⟨carrier, range⟩

public instance [Ord α] {s : RocSlice α β} : ToIterator s Id ((a : α) × β a) :=
  ToIterator.of (RxcIterator α β) (RocIterator s.1.treeMap s.1.range.lower s.1.range.upper)

public theorem toList_roc {α : Type u} {β : α → Type v} [Ord α] [TransOrd α] (t : Impl α β)
    (ordered : t.Ordered) (lowerBound upperBound : α) : t[lowerBound<...=upperBound].toList = t.toList.filter (fun e => (compare e.fst lowerBound).isGT ∧ (compare e.fst upperBound).isLE) := by
  simp only [Roc.Sliceable.mkSlice, Slice.toList_eq_toList_iter, Slice.iter,
    Slice.Internal.iter_eq_toIteratorIter, ToIterator.iter, ToIterator.iterM_eq,
    Iter.toIter_toIterM]
  rw [toList_rocIter]
  · exact ordered

end Roc

namespace Unit

public structure RocSliceData (α : Type u) [Ord α] where
  treeMap : Impl α (fun _ => Unit)
  range : Roc α

public abbrev RocSlice α [Ord α] := Slice (RocSliceData α)

public instance {α : Type u} [Ord α] : Roc.Sliceable (Impl α (fun _ => Unit)) α (Unit.RocSlice α) where
  mkSlice carrier range := ⟨carrier, range⟩

public instance [Ord α] {s : Unit.RocSlice α} : ToIterator s Id α := by
  apply ToIterator.of
  · exact (⟨RxcIterator.mk (Zipper.prependMapGT s.1.treeMap s.1.range.lower .done) s.1.range.upper⟩ : Iter _ ).map fun e => (e.1)

public theorem toList_roc {α : Type u} [Ord α] [TransOrd α] (t : Impl α (fun _ => Unit))
    (ordered : t.Ordered) (lowerBound upperBound: α) : (t : Impl α (fun _ => Unit))[lowerBound<...=upperBound].toList = (Internal.Impl.keys t).filter (fun e => (compare e lowerBound).isGT ∧ (compare e upperBound).isLE) := by
  simp only [Roc.Sliceable.mkSlice, Slice.toList_eq_toList_iter, Slice.iter,
    Slice.Internal.iter_eq_toIteratorIter, ToIterator.iter, ToIterator.iterM_eq,
    Iter.toIter_toIterM]
  rw [Iter.toList_map]
  have := @toList_rocIter α (fun _ => Unit) _ _ t ordered lowerBound upperBound
  rw [RocIterator] at this
  rw [this]
  have eq : (fun (e : (_ : α) × Unit) => decide ((compare e.fst lowerBound).isGT = true ∧ (compare e.fst upperBound).isLE = true)) =
    (fun (e : α) => decide ((compare e lowerBound).isGT = true ∧ (compare e upperBound).isLE = true)) ∘ (fun e => e.fst) := by congr
  conv =>
    lhs
    rhs
    rw [eq]
  rw [← List.filter_map, ← Std.DTreeMap.Internal.Impl.map_fst_toList_eq_keys]

end Unit

namespace Const

public structure RocSliceData (α : Type u) (β : Type v) [Ord α] where
  treeMap : Impl α (fun _ => β)
  range : Roc α

public abbrev RocSlice α β [Ord α] := Slice (RocSliceData α β)

public instance {α : Type u} {β : Type v} [Ord α] : Roc.Sliceable (Impl α (fun _ => β)) α (RocSlice α β) where
  mkSlice carrier range := ⟨carrier, range⟩

public instance [Ord α] {s : RocSlice α β} : ToIterator s Id (α × β) := by
  apply ToIterator.of
  · exact (⟨RxcIterator.mk (Zipper.prependMapGT s.1.treeMap s.1.range.lower .done) s.1.range.upper⟩ : Iter ((_ : α) × β)).map fun e => (e.1, e.2)

public theorem toList_roc {α : Type u} {β : Type v} [Ord α] [TransOrd α] (t : Impl α (fun _ => β))
    (ordered : t.Ordered) (lowerBound upperBound : α) : t[lowerBound<...=upperBound].toList = (Internal.Impl.Const.toList t).filter (fun e => (compare e.fst lowerBound).isGT ∧ (compare e.fst upperBound).isLE) := by
  simp only [Roc.Sliceable.mkSlice, Slice.toList_eq_toList_iter, Slice.iter,
    Slice.Internal.iter_eq_toIteratorIter, ToIterator.iter, ToIterator.iterM_eq,
    Iter.toIter_toIterM]
  rw [Iter.toList_map]
  have := @toList_rocIter α (fun _ => β) _ _ t ordered lowerBound upperBound
  rw [RocIterator] at this
  rw [this]
  have eq : (fun (e : (_ : α) × β) => decide ((compare e.fst lowerBound).isGT = true ∧ (compare e.fst upperBound).isLE = true)) =
    (fun (e : α × β) => decide ((compare e.fst lowerBound).isGT = true ∧ (compare e.fst upperBound).isLE = true)) ∘ (fun e => (e.1, e.2)) := by congr
  conv =>
    lhs
    rhs
    rw [eq]
  rw [← List.filter_map]
  congr
  rw [Impl.Const.toList_eq_toListModel_map, Impl.toList_eq_toListModel]

end Const

section Rci

@[always_inline]
public def RciIterator [Ord α] (t : Impl α β) (lowerBound : α) : Iter (α := Zipper α β) ((a : α) × β a) :=
  ⟨Zipper.prependMapGE t lowerBound .done⟩

theorem toList_rciIter {α β} [Ord α] [TransOrd α]
    {t : Impl α β} {t_ord : t.Ordered} {lowerBound : α} :
    (RciIterator t lowerBound : Iter (Sigma β)).toList =
      t.toList.filter (fun e => (compare e.fst lowerBound).isGE) := by
  simp only [RciIterator]
  have := @Zipper.toList_iter _ _ (Zipper.prependMapGE t lowerBound Zipper.done)
  simp only [Zipper.iter] at this
  simp only [this]
  rw [← Zipper.prependMap_pruneLE_eq_prependMapGE]
  · simp only [Zipper.toList_prependMap_eq_append, Zipper.toList, List.append_nil]
    apply Impl.toList_pruneLE
    exact t_ord
  · exact t_ord

public structure RciSliceData (α : Type u) (β : α → Type v) [Ord α] where
  treeMap : Impl α β
  range : Rci α

public abbrev RciSlice α β [Ord α] := Slice (RciSliceData α β)

public instance {α : Type u} {β : α → Type v} [Ord α] : Rci.Sliceable (Impl α β) α (RciSlice α β) where
  mkSlice carrier range := ⟨carrier, range⟩

public instance [Ord α] {s : RciSlice α β} : ToIterator s Id ((a : α) × β a) :=
  ToIterator.of (Zipper α β) (RciIterator s.1.treeMap s.1.range.lower)

public theorem toList_rci {α : Type u} {β : α → Type v} [Ord α] [TransOrd α] (t : Impl α β)
    (ordered : t.Ordered) (lowerBound : α) : t[lowerBound...*].toList = t.toList.filter (fun e => (compare e.fst lowerBound).isGE) := by
  simp only [Rci.Sliceable.mkSlice, Slice.toList_eq_toList_iter, Slice.iter,
    Slice.Internal.iter_eq_toIteratorIter, ToIterator.iter, ToIterator.iterM_eq,
    Iter.toIter_toIterM]
  rw [toList_rciIter]
  · exact ordered

end Rci

namespace Unit

public structure RciSliceData (α : Type u) [Ord α] where
  treeMap : Impl α (fun _ => Unit)
  range : Rci α

public abbrev RciSlice α [Ord α] := Slice (RciSliceData α)

public instance {α : Type u} [Ord α] : Rci.Sliceable (Impl α (fun _ => Unit)) α (Unit.RciSlice α) where
  mkSlice carrier range := ⟨carrier, range⟩

public instance [Ord α] {s : Unit.RciSlice α} : ToIterator s Id α := by
  apply ToIterator.of
  · exact (⟨Zipper.prependMapGE s.1.treeMap s.1.range.lower Zipper.done⟩ : Iter _ ).map fun e => (e.1)

public theorem toList_rci {α : Type u} [Ord α] [TransOrd α] (t : Impl α (fun _ => Unit))
    (ordered : t.Ordered) (lowerBound : α) : (t : Impl α (fun _ => Unit))[lowerBound...*].toList = (Internal.Impl.keys t).filter (fun e => (compare e lowerBound).isGE) := by
  simp only [Rci.Sliceable.mkSlice, Slice.toList_eq_toList_iter, Slice.iter,
    Slice.Internal.iter_eq_toIteratorIter, ToIterator.iter, ToIterator.iterM_eq,
    Iter.toIter_toIterM]
  rw [Iter.toList_map]
  rw [← Std.DTreeMap.Internal.Impl.map_fst_toList_eq_keys]
  rw [List.filter_map]
  congr
  have := @Zipper.toList_iter _ _ (Zipper.prependMapGE t lowerBound Zipper.done)
  simp only [Zipper.iter] at this
  simp only [this]
  rw [← Zipper.prependMap_pruneLE_eq_prependMapGE]
  · simp [Zipper.toList_prependMap_eq_append]
    rw [Impl.toList_pruneLE]
    simp [Impl.toList_eq_toListModel]
    congr
    · exact ordered
  · exact ordered

end Unit

namespace Const

public structure RciSliceData (α : Type u) (β : Type v) [Ord α] where
  treeMap : Impl α (fun _ => β)
  range : Rci α

public abbrev RciSlice α β [Ord α] := Slice (RciSliceData α β)

public instance {α : Type u} {β : Type v} [Ord α] : Rci.Sliceable (Impl α (fun _ => β)) α (RciSlice α β) where
  mkSlice carrier range := ⟨carrier, range⟩

public instance [Ord α] {s : RciSlice α β} : ToIterator s Id (α × β) := by
  apply ToIterator.of
  · exact (⟨(Zipper.prependMapGE s.1.treeMap s.1.range.lower Zipper.done)⟩ : Iter ((_ : α) × β)).map fun e => (e.1, e.2)

public theorem toList_rci {α : Type u} {β : Type v} [Ord α] [TransOrd α] (t : Impl α (fun _ => β))
    (ordered : t.Ordered) (lowerBound : α) : t[lowerBound...*].toList = (Internal.Impl.Const.toList t).filter (fun e => (compare e.fst lowerBound).isGE) := by
  simp only [Rci.Sliceable.mkSlice, Slice.toList_eq_toList_iter, Slice.iter,
    Slice.Internal.iter_eq_toIteratorIter, ToIterator.iter, ToIterator.iterM_eq,
    Iter.toIter_toIterM]
  rw [Iter.toList_map]
  rw [Impl.Const.toList_eq_toListModel_map]
  rw [List.filter_map]
  congr
  have := @Zipper.toList_iter _ _ (Zipper.prependMapGE t lowerBound Zipper.done)
  simp only [Zipper.iter] at this
  simp only [this]
  rw [← Zipper.prependMap_pruneLE_eq_prependMapGE]
  · simp [Zipper.toList_prependMap_eq_append]
    rw [Impl.toList_pruneLE]
    simp [Impl.toList_eq_toListModel]
    congr
    · exact ordered
  · exact ordered

end Const

section Roi

@[always_inline]
public def RoiIterator [Ord α] (t : Impl α β) (lowerBound : α) : Iter (α := Zipper α β) ((a : α) × β a) :=
  ⟨Zipper.prependMapGT t lowerBound .done⟩

theorem toList_roiIter {α β} [Ord α] [TransOrd α]
    {t : Impl α β} {t_ord : t.Ordered} {lowerBound : α} :
    (RoiIterator t lowerBound : Iter (Sigma β)).toList =
      t.toList.filter (fun e => (compare e.fst lowerBound).isGT) := by
  simp only [RoiIterator]
  have := @Zipper.toList_iter _ _ (Zipper.prependMapGT t lowerBound .done)
  simp only [Zipper.iter] at this
  rw [this]
  rw [← Zipper.prependMap_pruneLT_eq_prependMapGT]
  · simp only [Zipper.toList_prependMap_eq_append, Zipper.toList, List.append_nil]
    apply Impl.toList_pruneLT
    exact t_ord
  · exact t_ord

public structure RoiSliceData (α : Type u) (β : α → Type v) [Ord α] where
  treeMap : Impl α β
  range : Roi α

public abbrev RoiSlice α β [Ord α] := Slice (RoiSliceData α β)

public instance {α : Type u} {β : α → Type v} [Ord α] : Roi.Sliceable (Impl α β) α (RoiSlice α β) where
  mkSlice carrier range := ⟨carrier, range⟩

public instance [Ord α] {s : RoiSlice α β} : ToIterator s Id ((a : α) × β a) :=
  ToIterator.of (Zipper α β) (RoiIterator s.1.treeMap s.1.range.lower)

public theorem toList_roi {α : Type u} {β : α → Type v} [Ord α] [TransOrd α] (t : Impl α β)
    (ordered : t.Ordered) (lowerBound : α) : t[lowerBound<...*].toList = t.toList.filter (fun e => (compare e.fst lowerBound).isGT) := by
  simp only [Roi.Sliceable.mkSlice, Slice.toList_eq_toList_iter, Slice.iter,
    Slice.Internal.iter_eq_toIteratorIter, ToIterator.iter, ToIterator.iterM_eq,
    Iter.toIter_toIterM]
  rw [toList_roiIter]
  · exact ordered

end Roi

namespace Unit

public structure RoiSliceData (α : Type u) [Ord α] where
  treeMap : Impl α (fun _ => Unit)
  range : Roi α

public abbrev RoiSlice α [Ord α] := Slice (RoiSliceData α)

public instance {α : Type u} [Ord α] : Roi.Sliceable (Impl α (fun _ => Unit)) α (Unit.RoiSlice α) where
  mkSlice carrier range := ⟨carrier, range⟩

public instance [Ord α] {s : Unit.RoiSlice α} : ToIterator s Id α := by
  apply ToIterator.of
  · exact (⟨Zipper.prependMapGT s.1.treeMap s.1.range.lower Zipper.done⟩ : Iter _ ).map fun e => (e.1)

public theorem toList_roi {α : Type u} [Ord α] [TransOrd α] (t : Impl α (fun _ => Unit))
    (ordered : t.Ordered) (lowerBound : α) : (t : Impl α (fun _ => Unit))[lowerBound<...*].toList = (Internal.Impl.keys t).filter (fun e => (compare e lowerBound).isGT) := by
  simp only [Roi.Sliceable.mkSlice, Slice.toList_eq_toList_iter, Slice.iter,
    Slice.Internal.iter_eq_toIteratorIter, ToIterator.iter, ToIterator.iterM_eq,
    Iter.toIter_toIterM]
  rw [Iter.toList_map]
  rw [← Std.DTreeMap.Internal.Impl.map_fst_toList_eq_keys]
  rw [List.filter_map]
  congr
  have := @Zipper.toList_iter _ _ (Zipper.prependMapGT t lowerBound Zipper.done)
  simp only [Zipper.iter] at this
  simp only [this]
  rw [← Zipper.prependMap_pruneLT_eq_prependMapGT]
  · simp [Zipper.toList_prependMap_eq_append]
    rw [Impl.toList_pruneLT]
    simp [Impl.toList_eq_toListModel]
    congr
    · exact ordered
  · exact ordered

end Unit

namespace Const

public structure RoiSliceData (α : Type u) (β : Type v) [Ord α] where
  treeMap : Impl α (fun _ => β)
  range : Roi α

public abbrev RoiSlice α β [Ord α] := Slice (RoiSliceData α β)

public instance {α : Type u} {β : Type v} [Ord α] : Roi.Sliceable (Impl α (fun _ => β)) α (RoiSlice α β) where
  mkSlice carrier range := ⟨carrier, range⟩

public instance [Ord α] {s : RoiSlice α β} : ToIterator s Id (α × β) := by
  apply ToIterator.of
  · exact (⟨(Zipper.prependMapGT s.1.treeMap s.1.range.lower .done)⟩ : Iter ((_ : α) × β)).map fun e => (e.1, e.2)

public theorem toList_roi {α : Type u} {β : Type v} [Ord α] [TransOrd α] (t : Impl α (fun _ => β))
    (ordered : t.Ordered) (lowerBound : α) : t[lowerBound<...*].toList = (Internal.Impl.Const.toList t).filter (fun e => (compare e.fst lowerBound).isGT) := by
  simp only [Roi.Sliceable.mkSlice, Slice.toList_eq_toList_iter, Slice.iter,
    Slice.Internal.iter_eq_toIteratorIter, ToIterator.iter, ToIterator.iterM_eq,
    Iter.toIter_toIterM]
  rw [Iter.toList_map]
  have := @toList_roiIter α (fun _ => β) _ _ t ordered lowerBound
  rw [RoiIterator] at this
  rw [this]
  have eq : (fun (e : (_ : α) × β) => ((compare e.fst lowerBound).isGT)) = ((fun (e : α × β) => ((compare e.fst lowerBound).isGT)) ∘ (fun e => (e.1,e.2))) := by congr
  conv =>
    lhs
    rhs
    rw [eq]
  rw [← List.filter_map]
  congr
  rw [Impl.Const.toList_eq_toListModel_map, Impl.toList_eq_toListModel]

end Const


section Rii

public def RiiIterator (t : Impl α β) : Iter (α := Zipper α β) ((a : α) × β a) :=
  ⟨Zipper.prependMap t .done⟩

theorem toList_riiIter {α β}
    {t : Impl α β} :
    (RiiIterator t : Iter (Sigma β)).toList =
      t.toList := by
  simp only [RiiIterator]
  have := @Zipper.toList_iter _ _ (Zipper.prependMap t .done)
  simp only [Zipper.iter] at this
  rw [this]
  simp only [Zipper.toList_prependMap_eq_append, Zipper.toList, List.append_nil]

public structure RiiSliceData (α : Type u) (β : α → Type v) where
  treeMap : Impl α β
  range : Rii α

public abbrev RiiSlice α β := Slice (RiiSliceData α β)

public instance {α : Type u} {β : α → Type v} : Rii.Sliceable (Impl α β) α (RiiSlice α β) where
  mkSlice carrier range := ⟨carrier, range⟩

public instance {s : RiiSlice α β} : ToIterator s Id ((a : α) × β a) :=
  ToIterator.of (Zipper α β) (RiiIterator s.1.treeMap)

public theorem toList_rii {α : Type u} {β : α → Type v} (t : Impl α β) : t[*...*].toList = t.toList := by
  simp only [Rii.Sliceable.mkSlice, Slice.toList_eq_toList_iter, Slice.iter,
    Slice.Internal.iter_eq_toIteratorIter, ToIterator.iter, ToIterator.iterM_eq,
    Iter.toIter_toIterM]
  rw [toList_riiIter]

end Rii

namespace Unit

public structure RiiSliceData (α : Type u) where
  treeMap : Impl α (fun _ => Unit)
  range : Rii α

public abbrev RiiSlice α  := Slice (RiiSliceData α)

public instance {α : Type u} : Rii.Sliceable (Impl α (fun _ => Unit)) α (Unit.RiiSlice α) where
  mkSlice carrier range := ⟨carrier, range⟩

public instance {s : Unit.RiiSlice α} : ToIterator s Id α := by
  apply ToIterator.of
  · exact (⟨Zipper.prependMap s.internalRepresentation.treeMap .done⟩ : Iter _ ).map fun e => (e.1)

public theorem toList_rii {α : Type u} (t : Impl α (fun _ => Unit)) :
    (t : Impl α fun _ => Unit)[*...*].toList = Internal.Impl.keys t := by
  simp only [Rii.Sliceable.mkSlice, Slice.toList_eq_toList_iter, Slice.iter,
    Slice.Internal.iter_eq_toIteratorIter, ToIterator.iter, ToIterator.iterM_eq,
    Iter.toIter_toIterM]
  rw [Iter.toList_map]
  rw [← Std.DTreeMap.Internal.Impl.map_fst_toList_eq_keys]
  congr
  have := @Zipper.toList_iter _ _ (Zipper.prependMap t .done)
  simp only [Zipper.iter] at this
  rw [this]
  simp [Zipper.toList_prependMap_eq_append, Zipper.toList, Impl.toList_eq_toListModel]

end Unit

namespace Const

public structure RiiSliceData (α : Type u) (β : Type v) where
  treeMap : Impl α (fun _ => β)
  range : Rii α

public abbrev RiiSlice α β  := Slice (RiiSliceData α β)

public instance {α : Type u} {β : Type v} : Rii.Sliceable (Impl α (fun _ => β)) α (Const.RiiSlice α β) where
  mkSlice carrier range := ⟨carrier, range⟩

public instance {s : Const.RiiSlice α β} : ToIterator s Id (α × β) := by
  apply ToIterator.of
  · exact (⟨Zipper.prependMap s.internalRepresentation.treeMap .done⟩ : Iter ((_ : α) × β)).map fun e => (e.1, e.2)

public theorem toList_rii {α : Type u} {β : Type v} (t : Impl α (fun _ => β)) :
    (t : Impl α fun _ => β)[*...*].toList = Internal.Impl.Const.toList t := by
  simp only [Rii.Sliceable.mkSlice, Slice.toList_eq_toList_iter, Slice.iter,
    Slice.Internal.iter_eq_toIteratorIter, ToIterator.iter, ToIterator.iterM_eq,
    Iter.toIter_toIterM]
  rw [Iter.toList_map]
  rw [Impl.Const.toList_eq_toListModel_map]
  congr
  have := @Zipper.toList_iter _ _ (Zipper.prependMap t .done)
  simp only [Zipper.iter] at this
  rw [this]
  simp [Zipper.toList_prependMap_eq_append, Zipper.toList, Impl.toList_eq_toListModel]

end Const

end Std.DTreeMap.Internal
