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

theorem pruneLE_eq_filter {α β} [Ord α] [TransOrd α] (t : Internal.Impl α β) (ord_t : t.Ordered) (lowerBound : α) :
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
      suffices new_goal : List.filter (fun e => (compare e.fst lowerBound).isGE) l.toListModel = [] from by
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
      suffices new_goal : List.filter (fun e => (compare e.fst lowerBound).isGE) l.toListModel = [] from by
        simp only [new_goal, List.nil_append]
        simp only [toList_eq_toListModel] at r_ih
        apply r_ih
        exact Internal.Impl.Ordered.right ord_t
      rw [List.filter_eq_nil_iff]
      intro a mem
      simp only [Bool.not_eq_true, Ordering.isGE_eq_false]
      exact TransCmp.lt_trans (Internal.Impl.Ordered.compare_left ord_t mem) heq

theorem pruneLT_eq_filter {α β} [Ord α] [TransOrd α] (t : Internal.Impl α β) (ord_t : t.Ordered) (lowerBound : α) :
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
          List.filter (fun e => (compare e.fst lowerBound).isGT) r.toListModel = r.toListModel from by
        simp only [new_goal, Ordering.isGT_eq, List.nil_append]
      apply And.intro
      . rw [List.filter_eq_nil_iff]
        intro a mem
        simp only [Ordering.isGT_iff_eq_gt, ← Ordering.isLE_iff_ne_gt]
        apply TransOrd.isLE_trans _ (Ordering.isLE_of_eq_eq heq)
        apply Ordering.isLE_of_eq_lt
        exact Internal.Impl.Ordered.compare_left ord_t mem
      . apply List.filter_eq_self.2
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

theorem Zipper.prepend_pruneLE_eq_prependMapGE [Ord α] (t : Impl α β) (ord_t : t.Ordered)
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

theorem Zipper.prepend_eq_prependMapGT_self [Ord α] [TransOrd α] (r : Impl α β)
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
    . exact (Impl.Ordered.left ord_r)
    . intro e mem
      apply hyp e
      simp only [Impl.toList_eq_toListModel, Impl.toListModel_inner,
        List.mem_append, List.mem_cons]
      apply Or.inl
      . rw [Impl.toList_eq_toListModel] at mem
        exact mem

theorem Zipper.prepend_pruneLT_eq_prependMapGT [Ord α] [TransOrd α] (t : Impl α β)
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
      apply prepend_eq_prependMapGT_self
      . exact Impl.Ordered.right ord_t
      . intro e mem
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
    (hyp : ∀ k ∈ z.toList, ∀ k' ∈ t.toListModel, compare k'.1 k.1 = .lt ) :
    (Zipper.prependMap t z).Ordered := by
  induction t generalizing z
  case leaf =>
    rw [prependMap]
    exact ord_z
  case inner _ k v l r l_ih r_ih =>
    rw [prependMap]
    apply l_ih
    . exact Impl.Ordered.left ord_t
    . rw [Zipper.Ordered]
      simp only [Zipper.toList]
      simp
      apply And.intro
      . intro a hyp
        cases hyp
        . rename_i in_r
          rw [Impl.toList_eq_toListModel] at in_r
          exact @Impl.Ordered.compare_right α β _ _ k v l r ord_t a in_r
        . rename_i in_r
          specialize hyp a in_r ⟨k,v⟩
          simp at hyp
          exact hyp
      . have := @r_ih (Impl.Ordered.right ord_t) z ord_z
        simp only [Ordered, Zipper.toList_prependMap_eq_append] at this
        . apply this
          intro k₁ mem₁ k₂ mem₂
          specialize hyp k₁ mem₁ k₂ (by simp only [Impl.toListModel_inner,
            List.mem_append, List.mem_cons, mem₂, or_true])
          exact hyp
    . intro k₁ mem₁ k₂ mem₂
      simp only [toList, List.cons_append, List.mem_cons, List.mem_append] at mem₁
      apply Or.elim mem₁
      . intro eq_key
        rw [eq_key]
        exact Impl.Ordered.compare_left ord_t mem₂
      . intro hyp₂
        apply Or.elim hyp₂
        . intro in_r
          apply TransCmp.lt_trans
          . exact Impl.Ordered.compare_left ord_t mem₂
          . rw [Impl.toList_eq_toListModel] at in_r
            exact Impl.Ordered.compare_right ord_t in_r
        . intro in_z
          apply hyp k₁ in_z k₂
          simp only [Impl.toListModel_inner, List.mem_append, mem₂, List.mem_cons, true_or]

theorem Zipper.ordered_prependMap_done [Ord α] [TransOrd α] {t : Impl α β}
    {ord_t : t.Ordered} :
    (Zipper.prependMap t .done).Ordered := by
  apply ordered_prependMap
  . exact ord_t
  . simp only [Ordered, toList, List.Pairwise.nil]
  simp only [toList, List.not_mem_nil, false_implies, implies_true]

theorem Zipper.ordered_of_cons_ordered [Ord α] [TransOrd α] {t : Impl α β}
    {z : Zipper α β} : (Zipper.cons k v t z).Ordered → z.Ordered := by
  intro hyp
  simp only [Zipper.Ordered, Zipper.toList] at hyp
  simp only [Ordered]
  exact List.Pairwise.sublist (List.sublist_append_right (⟨k, v⟩ :: t.toList) z.toList) hyp

theorem Zipper.prependMap_size (t : Impl α β) (it : Zipper α β) : (Zipper.prependMap t it).size = t.treeSize + it.size := by
  fun_induction Zipper.prependMap
  case case1 =>
   simp only [Impl.treeSize, Nat.zero_add]
  case case2 size k v l r it ih =>
    simp only [ih, Zipper.size, Impl.treeSize, ← Nat.add_assoc, Nat.add_comm]

public def Zipper.step : Zipper α β → IterStep (IterM (α := Zipper α β) Id ((a : α) × β a)) ((a : α) × β a)
  | .done => .done
  | .cons k v t it=>
      .yield ⟨it.prependMap t⟩ ⟨k, v⟩

public instance : Iterator (Zipper α β) Id ((a : α) × β a) where
  IsPlausibleStep it step := it.internalState.step = step
  step it := ⟨it.internalState.step, rfl⟩

public instance : IteratorCollect (Zipper α β) Id Id := .defaultImplementation

public instance : IteratorCollectPartial (Zipper α β) Id Id := .defaultImplementation

def Zipper.instFinitenessRelation : FinitenessRelation (Zipper α β) Id where
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
          simp only [h2, ← h'.1, Zipper.prependMap_size, Zipper.size, Nat.add_lt_add_iff_right,
            Nat.lt_add_left_iff_pos, Nat.lt_add_one]

@[no_expose]
public instance Zipper.instFinite : Finite (Zipper α β) Id :=
  .of_finitenessRelation Zipper.instFinitenessRelation

public def Zipper.iter (t : Zipper α β) : Iter (α := Zipper α β) ((a : α) × β a) := ⟨t⟩

public def Zipper.iterOfTree (t : Impl α β) : Iter (α := Zipper α β) ((a : α) × β a) :=
  Zipper.iter <| Zipper.done.prependMap t

public instance {z : Zipper α β} : ToIterator z Id ((a : α) × β a) where
  State := Zipper α β
  iterMInternal := Iter.toIterM <| Zipper.iter z

theorem Zipper.step_eq_match {it : IterM (α := Zipper α β) Id ((a : α) × β a)} :
    it.step = ⟨match it.internalState.iter with
    | ⟨Zipper.done⟩ => IterStep.done
    | ⟨Zipper.cons k v t z⟩ => IterStep.yield { internalState := Zipper.prependMap t z } ⟨k, v⟩,
    (by
      simp only [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, Zipper.step]; split; all_goals (rename_i heq; simp only [Zipper.iter,
        heq]))⟩ := by
  simp only [IterM.step, Iterator.step, Zipper.step]
  congr 1
  cases it
  next =>
    rename_i internalState
    simp
    congr 1
    cases internalState
    case done =>
      simp only [Zipper.iter]
    case cons k v tree next =>
      simp only [Zipper.iter]

theorem Zipper.val_step_Zipper_eq_match {α β}
    {it : Iter (α := Zipper α β) (Sigma β)} :
    it.step.val =
        match it.internalState.iter with
        | ⟨Zipper.done⟩ => IterStep.done
        | ⟨Zipper.cons k v t it'⟩ =>
            IterStep.yield { internalState := Zipper.prependMap t it' } ⟨k, v⟩
        := by
  rcases it with ⟨z, upper⟩
  rw [Iter.step]
  rw [Zipper.step_eq_match]
  simp only [Iter.toIterM]
  split
  · simp only [IterM.Step.toPure, IterStep.mapIterator, Id.run, Zipper.iter]
  · rename_i heq
    simp only [Zipper.iter, Iter.mk.injEq, reduceCtorEq] at heq
  . split
    case h_1 =>
      rename_i heq
      simp only [Zipper.iter, Iter.mk.injEq, reduceCtorEq] at heq
    case h_2 k v tree next x k v t it' heq =>
      simp only [Zipper.iter] at heq
      injections
      rename_i k_eq v_eq tree_eq next_eq
      simp only [Iter.step, Iter.toIterM, Id.run, IterM.step, Iterator.step, Zipper.step,
        IterM.Step.toPure_yield, PlausibleIterStep.yield, IterM.toIter, IterStep.yield.injEq,
        Iter.mk.injEq, Sigma.mk.injEq]
      simp_all

theorem Zipper.toList_iter {α β} {z : Zipper α β}: z.iter.toList = z.toList := by
  rw [Iter.toList_eq_match_step]
  generalize hit : (z.iter.step.val) = step
  rw [val_step_Zipper_eq_match] at hit
  split at hit <;> rename_i heq
  · simp only [← hit, List.nil_eq]
    cases z
    . rw [Zipper.toList]
    . simp only [Zipper.iter, Iter.mk.injEq, reduceCtorEq] at heq
  . rename_i x k v t it'
    simp only [← hit]
    have := @Zipper.toList_iter α β (prependMap t it')
    simp only [iter] at this
    rw [this]
    . generalize heq2 : Zipper.cons k v t it' = y
      rw [heq2] at heq
      simp only [Zipper.iter, Iter.mk.injEq] at heq
      rw [heq]
      rw [← heq2]
      simp only [Zipper.toList, List.cons_append, List.cons.injEq, true_and]
      rw [Zipper.toList_prependMap_eq_append]
termination_by z.size
decreasing_by
  simp_all
  rename_i t _ _ heq
  simp only [Zipper.iter, Iter.mk.injEq] at heq
  rw [heq]
  simp only [Zipper.size]
  induction t
  case leaf =>
    simp only [Zipper.prependMap, Impl.treeSize, Nat.add_zero, Nat.lt_add_left_iff_pos,
      Nat.lt_add_one]
  case inner =>
    simp only [Zipper.prependMap_size, Impl.treeSize, Nat.add_lt_add_iff_right, Nat.lt_add_left_iff_pos,
      Nat.lt_add_one]

public theorem Zipper.iterOfTree_toList_eq_toList (t : Impl α β) :
    (Zipper.iterOfTree t).toList = t.toList := by
  unfold iterOfTree
  unfold iter
  have := @Zipper.toList_iter α β (prependMap t .done)
  simp only [iter] at this
  rw [this]
  simp only [Zipper.toList_prependMap_eq_append, toList, List.append_nil]

public theorem Zipper.map_iterOfTree_eq_tree_toList_map (t : Impl α β) :
   (Iter.map f (Internal.Zipper.iterOfTree t)).toList = List.map f t.toList := by
  rw [Iter.toList_map]
  congr
  unfold iterOfTree
  rw [@toList_iter α β (prependMap t .done)]
  simp [Zipper.toList_prependMap_eq_append, toList]

def Zipper.instProductivenessRelation : ProductivenessRelation (Zipper α β) Id where
  rel x x' := x.1.size < x'.1.size
  wf := by
    apply InvImage.wf
    exact Nat.lt_wfRel.wf
  subrelation {it it'} h := by
    simp [IterM.IsPlausibleSkipSuccessorOf, IterM.IsPlausibleStep, Iterator.IsPlausibleStep] at h
    have := @Zipper.step_eq_match α β ⟨it.1⟩
    simp [IterM.step, Iterator.step] at this
    injections val_eq
    rw [h] at val_eq
    split at val_eq <;> contradiction

@[no_expose]
public instance instProductive : Productive (Zipper α β) Id :=
  .of_productivenessRelation Zipper.instProductivenessRelation

theorem Zipper.val_step_map_Zipper_eq_match {α β γ} {f : (a : α) × β a → γ}
    {it : Iter (α := Zipper α β) (Sigma β)} :
    (it.map f).step.val =
        match it.internalState.iter with
        | ⟨Zipper.done⟩ => IterStep.done
        | ⟨Zipper.cons k v t it'⟩ =>
            IterStep.yield (({internalState := Zipper.prependMap t it' : Iter (α := Zipper α β) (Sigma β)}).map f) (f ⟨k, v⟩) := by
  simp [Iter.step_map]
  generalize heq : it.step = x
  have := @val_step_Zipper_eq_match _ _ it
  rcases x with ⟨val, prop⟩
  simp [heq] at this
  split at this <;> (rename_i heq2 ; simp [heq2, this])

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

public instance [Ord α] : IteratorCollectPartial (RxcIterator α β) Id Id := .defaultImplementation

def instFinitenessRelation [Ord α] : FinitenessRelation (RxcIterator α β) Id where
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
      . split at h'
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
          simp only [h2, ← h'.1, Zipper.prependMap_size, Zipper.size, Nat.add_lt_add_iff_right,
            Nat.lt_add_left_iff_pos, Nat.lt_add_one]

@[no_expose]
public instance instFinite [Ord α] : Finite (RxcIterator α β) Id :=
  .of_finitenessRelation instFinitenessRelation

public theorem step_rxcIterator_eq_match [Ord α] {it : IterM (α := RxcIterator α β) Id ((a : α) × β a)} :
    it.step = ⟨match it.internalState.iter with
    | Zipper.done => IterStep.done
    | Zipper.cons k v t z =>
      if (compare k it.internalState.upper).isLE = true then
        IterStep.yield { internalState := { iter := Zipper.prependMap t z, upper := it.internalState.upper } } ⟨k, v⟩
      else IterStep.done,
    (by simp only [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, RxcIterator.step]; split; all_goals (rename_i heq; simp only [heq]))⟩ := by
  simp only [IterM.step, Iterator.step, RxcIterator.step]
  ext
  congr 1
  congr 1
  cases it
  next =>
    rename_i internalState
    simp
    cases internalState
    case mk iter upper =>
      simp
      cases iter
      case done =>
        simp only
      case cons k v tree next =>
        simp only

public theorem val_step_rxcIterator_eq_match {α β} [Ord α]
    {it : Iter (α := RxcIterator α β) (Sigma β)} :
    it.step.val =
        match it.internalState.iter with
        | Zipper.done => IterStep.done
        | Zipper.cons k v t it' =>
          if (compare k it.internalState.upper).isLE = true then
            IterStep.yield { internalState := { iter := Zipper.prependMap t it', upper := it.internalState.upper } } ⟨k, v⟩
          else IterStep.done := by
  rcases it with ⟨z, upper⟩
  rw [Iter.step]
  rw [step_rxcIterator_eq_match]
  simp only [Iter.toIterM]
  split
  · simp only [IterM.Step.toPure, IterStep.mapIterator, Id.run]
  · split <;> simp only [IterM.Step.toPure, IterM.toIter, IterStep.mapIterator, Id.run]

public theorem toList_rxcIter {α β} [Ord α]
    {z : Zipper α β} {bound : α} :
    (⟨RxcIterator.mk z bound⟩ : Iter (Sigma β)).toList =
      z.toList.takeWhile (fun e => (compare e.fst bound).isLE) := by
  rw [Iter.toList_eq_match_step]
  generalize hit : (⟨RxcIterator.mk z bound⟩ : Iter (Sigma β)).step.val = step
  rw [val_step_rxcIterator_eq_match] at hit
  simp only at hit
  split at hit <;> rename_i heq
  · simp only [← hit, Zipper.toList, List.takeWhile_nil]
  · split at hit
    · simp only [← hit, Zipper.toList, List.cons_append]
      rw [List.takeWhile_cons_of_pos ‹_›]
      simp
      rw [toList_rxcIter, Zipper.toList_prependMap_eq_append]
    · simp only [← hit, Zipper.toList, List.cons_append, List.nil_eq]
      rw [List.takeWhile_cons_of_neg ‹_›]
termination_by z.size
decreasing_by
  simp_all [Zipper.size, Zipper.prependMap_size]

public theorem toList_eq_takeWhile_list {α : Type u} {β : α → Type v} [Ord α] [TransOrd α] {bound : α} {l : List ((a : α) × β a)}
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
        . rw [← OrientedOrd.eq_swap] at this
          . exact this
        . exact heq

public theorem toList_eq_takeWhile {α β} [Ord α] [TransOrd α] {z : Zipper α β} {bound : α} {z_ord : z.Ordered} :
    z.toList.takeWhile (fun e => (compare e.fst bound).isLE) = z.toList.filter (fun e => (compare e.fst bound).isLE) := by
  simp only [Zipper.Ordered] at z_ord
  apply toList_eq_takeWhile_list
  exact z_ord

def instProductivenessRelation [Ord α] : ProductivenessRelation (RxcIterator α β) Id where
  rel t' t := t'.internalState.iter.size < t.internalState.iter.size
  wf := by
    apply InvImage.wf
    exact Nat.lt_wfRel.wf
  subrelation {it it'} h := by
    simp [IterM.IsPlausibleSkipSuccessorOf, IterM.IsPlausibleStep, Iterator.IsPlausibleStep] at h
    have := @step_rxcIterator_eq_match α β _ ⟨it.1⟩
    simp [IterM.step, Iterator.step] at this
    injections val_eq
    rw [h] at val_eq
    split at val_eq
    case h_1 => contradiction
    case h_2 =>
      split at val_eq <;> contradiction

@[no_expose]
public instance RxcIterator.instProductive [Ord α] : Productive (RxcIterator α β) Id :=
  .of_productivenessRelation instProductivenessRelation

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

public instance [Ord α] : IteratorCollectPartial (RxoIterator α β) Id Id := .defaultImplementation

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
      . split at h'
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
          simp only [h2, ← h'.1, Zipper.prependMap_size, Zipper.size, Nat.add_lt_add_iff_right,
            Nat.lt_add_left_iff_pos, Nat.lt_add_one]

@[no_expose]
public instance Rxo.instFinite [Ord α] : Finite (RxoIterator α β) Id :=
  .of_finitenessRelation RxoIterator.instFinitenessRelation

public theorem step_rxoIterator_eq_match [Ord α] {it : IterM (α := RxoIterator α β) Id ((a : α) × β a)} :
    it.step = ⟨match it.internalState.iter with
    | Zipper.done => IterStep.done
    | Zipper.cons k v t z =>
      if (compare k it.internalState.upper).isLT = true then
        IterStep.yield { internalState := { iter := Zipper.prependMap t z, upper := it.internalState.upper } } ⟨k, v⟩
      else IterStep.done,
    (by simp only [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, RxoIterator.step]; split; all_goals (rename_i heq; simp only [heq]))⟩ := by
  simp only [IterM.step, Iterator.step, RxoIterator.step]
  ext
  congr 1
  congr 1
  cases it
  next =>
    rename_i internalState
    simp
    cases internalState
    case mk iter upper =>
      simp
      cases iter
      case done =>
        simp only
      case cons k v tree next =>
        simp only

public theorem val_step_rxoIterator_eq_match {α β} [Ord α]
    {it : Iter (α := RxoIterator α β) (Sigma β)} :
    it.step.val =
        match it.internalState.iter with
        | Zipper.done => IterStep.done
        | Zipper.cons k v t it' =>
          if (compare k it.internalState.upper).isLT = true then
            IterStep.yield { internalState := { iter := Zipper.prependMap t it', upper := it.internalState.upper } } ⟨k, v⟩
          else IterStep.done := by
  rcases it with ⟨z, upper⟩
  rw [Iter.step]
  rw [step_rxoIterator_eq_match]
  simp only [Iter.toIterM]
  split
  · simp only [IterM.Step.toPure, IterStep.mapIterator, Id.run]
  · split <;> simp only [IterM.Step.toPure, IterM.toIter, IterStep.mapIterator, Id.run]

public theorem toList_rxoIter {α β} [Ord α]
    {z : Zipper α β} {bound : α} :
    (⟨RxoIterator.mk z bound⟩ : Iter (Sigma β)).toList =
      z.toList.takeWhile (fun e => (compare e.fst bound).isLT) := by
  rw [Iter.toList_eq_match_step]
  generalize hit : (⟨RxoIterator.mk z bound⟩ : Iter (Sigma β)).step.val = step
  rw [val_step_rxoIterator_eq_match] at hit
  simp only at hit
  split at hit <;> rename_i heq
  · simp only [← hit, Zipper.toList, List.takeWhile_nil]
  · split at hit
    · simp only [← hit, Zipper.toList, List.cons_append]
      rw [List.takeWhile_cons_of_pos ‹_›]
      simp
      rw [toList_rxoIter, Zipper.toList_prependMap_eq_append]
    · simp only [← hit, Zipper.toList, List.cons_append, List.nil_eq]
      rw [List.takeWhile_cons_of_neg ‹_›]
termination_by z.size
decreasing_by
  simp_all [Zipper.size, Zipper.prependMap_size]

public theorem toList_eq_takeWhile_list_LT {α : Type u} {β : α → Type v} [Ord α] [TransOrd α] {bound : α} {l : List ((a : α) × β a)}
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
        . apply Ordering.isGE_of_eq_gt this
        . exact heq

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
  rw [toList_rxcIter, toList_eq_takeWhile_list]
  . rw [Zipper.toList_prependMap_eq_append]
    simp [Zipper.toList]
  . apply Zipper.ordered_prependMap_done
    . exact ordered

end Ric

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
  rw [toList_rxoIter, toList_eq_takeWhile_list_LT]
  . rw [Zipper.toList_prependMap_eq_append]
    simp [Zipper.toList]
  . apply Zipper.ordered_prependMap_done
    . exact ordered

end Rio

section Rcc

@[always_inline]
public def RccIterator [Ord α] (t : Impl α β) (lowerBound : α) (upperBound : α)  : Iter (α := RxcIterator α β) ((a : α) × β a) :=
  ⟨RxcIterator.mk (Zipper.prependMapGE t lowerBound .done) upperBound⟩

public theorem toList_rccIter {α β} [Ord α] [TransOrd α]
    {t : Impl α β} {t_ord : t.Ordered} {lowerBound upperBound : α} :
    (RccIterator t lowerBound upperBound : Iter (Sigma β)).toList =
      t.toList.filter (fun e => (compare e.fst lowerBound).isGE ∧ (compare e.fst upperBound).isLE) := by
  simp only [RccIterator, Bool.decide_and, Bool.decide_eq_true]
  rw [toList_rxcIter, toList_eq_takeWhile_list]
  . conv =>
      rhs
      lhs
      ext x
      rw [Bool.and_comm]
    rw [← List.filter_filter]
    congr 1
    rw [← Zipper.prepend_pruneLE_eq_prependMapGE]
    . rw [Zipper.toList_prependMap_eq_append]
      rw [Impl.pruneLE_eq_filter]
      . simp [Zipper.toList]
      . exact t_ord
    . exact t_ord
  . rw [← Zipper.prepend_pruneLE_eq_prependMapGE]
    . simp only [Zipper.toList_prependMap_eq_append, Zipper.toList, List.append_nil]
      rw [Impl.pruneLE_eq_filter]
      . apply List.Pairwise.filter
        simp only [Impl.Ordered] at t_ord
        rw [Impl.toList_eq_toListModel]
        exact t_ord
      . exact t_ord
    . exact t_ord

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
  . exact ordered

end Rcc

section Rco

@[always_inline]
public def RcoIterator [Ord α] (t : Impl α β) (lowerBound : α) (upperBound : α)  : Iter (α := RxoIterator α β) ((a : α) × β a) :=
  ⟨RxoIterator.mk (Zipper.prependMapGE t lowerBound .done) upperBound⟩

public theorem toList_rcoIter {α β} [Ord α] [TransOrd α]
    {t : Impl α β} {t_ord : t.Ordered} {lowerBound upperBound : α} :
    (RcoIterator t lowerBound upperBound : Iter (Sigma β)).toList =
      t.toList.filter (fun e => (compare e.fst lowerBound).isGE ∧ (compare e.fst upperBound).isLT) := by
  simp only [RcoIterator, Bool.decide_and, Bool.decide_eq_true]
  rw [toList_rxoIter, toList_eq_takeWhile_list_LT]
  . conv =>
      rhs
      lhs
      ext x
      rw [Bool.and_comm]
    rw [← List.filter_filter]
    congr 1
    rw [← Zipper.prepend_pruneLE_eq_prependMapGE]
    . rw [Zipper.toList_prependMap_eq_append]
      rw [Impl.pruneLE_eq_filter]
      . simp only [Zipper.toList, List.append_nil]
      . exact t_ord
    . exact t_ord
  . rw [← Zipper.prepend_pruneLE_eq_prependMapGE]
    . simp only [Zipper.toList_prependMap_eq_append, Zipper.toList, List.append_nil]
      rw [Impl.pruneLE_eq_filter]
      . apply List.Pairwise.filter
        simp only [Impl.Ordered] at t_ord
        rw [Impl.toList_eq_toListModel]
        exact t_ord
      . exact t_ord
    . exact t_ord

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
  . exact ordered

end Rco

section Roo
@[always_inline]
public def RooIterator [Ord α] (t : Impl α β) (lowerBound : α) (upperBound : α)  : Iter (α := RxoIterator α β) ((a : α) × β a) :=
  ⟨RxoIterator.mk (Zipper.prependMapGT t lowerBound .done) upperBound⟩

public theorem toList_rooIter {α β} [Ord α] [TransOrd α]
    {t : Impl α β} {t_ord : t.Ordered} {lowerBound upperBound : α} :
    (RooIterator t lowerBound upperBound : Iter (Sigma β)).toList =
      t.toList.filter (fun e => (compare e.fst lowerBound).isGT ∧ (compare e.fst upperBound).isLT) := by
  simp only [RooIterator, Bool.decide_and, Bool.decide_eq_true]
  rw [toList_rxoIter, toList_eq_takeWhile_list_LT]
  . conv =>
      rhs
      lhs
      ext x
      rw [Bool.and_comm]
    rw [← List.filter_filter]
    congr 1
    rw [← Zipper.prepend_pruneLT_eq_prependMapGT]
    . rw [Zipper.toList_prependMap_eq_append]
      rw [Impl.pruneLT_eq_filter]
      . simp only [Zipper.toList, List.append_nil]
      . exact t_ord
    . exact t_ord
  . rw [← Zipper.prepend_pruneLT_eq_prependMapGT]
    . simp only [Zipper.toList_prependMap_eq_append, Zipper.toList, List.append_nil]
      rw [Impl.pruneLT_eq_filter]
      . apply List.Pairwise.filter
        simp only [Impl.Ordered] at t_ord
        rw [Impl.toList_eq_toListModel]
        exact t_ord
      . exact t_ord
    . exact t_ord

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
  . exact ordered

end Roo

section Roc
@[always_inline]
public def RocIterator [Ord α] (t : Impl α β) (lowerBound : α) (upperBound : α)  : Iter (α := RxcIterator α β) ((a : α) × β a) :=
  ⟨RxcIterator.mk (Zipper.prependMapGT t lowerBound .done) upperBound⟩

public theorem toList_rocIter {α β} [Ord α] [TransOrd α]
    {t : Impl α β} {t_ord : t.Ordered} {lowerBound upperBound : α} :
    (RocIterator t lowerBound upperBound : Iter (Sigma β)).toList =
      t.toList.filter (fun e => (compare e.fst lowerBound).isGT ∧ (compare e.fst upperBound).isLE) := by
  simp only [RocIterator, Bool.decide_and, Bool.decide_eq_true]
  rw [toList_rxcIter, toList_eq_takeWhile_list]
  . conv =>
      rhs
      lhs
      ext x
      rw [Bool.and_comm]
    rw [← List.filter_filter]
    congr 1
    rw [← Zipper.prepend_pruneLT_eq_prependMapGT]
    . rw [Zipper.toList_prependMap_eq_append]
      rw [Impl.pruneLT_eq_filter]
      . simp only [Zipper.toList, List.append_nil]
      . exact t_ord
    . exact t_ord
  . rw [← Zipper.prepend_pruneLT_eq_prependMapGT]
    . simp only [Zipper.toList_prependMap_eq_append, Zipper.toList, List.append_nil]
      rw [Impl.pruneLT_eq_filter]
      . apply List.Pairwise.filter
        simp only [Impl.Ordered] at t_ord
        rw [Impl.toList_eq_toListModel]
        exact t_ord
      . exact t_ord
    . exact t_ord

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
  . exact ordered

end Roc

section Rci
@[always_inline]
public def RciIterator [Ord α] (t : Impl α β) (lowerBound : α) : Iter (α := Zipper α β) ((a : α) × β a) :=
  ⟨Zipper.prependMapGE t lowerBound .done⟩

public theorem toList_rciIter {α β} [Ord α] [TransOrd α]
    {t : Impl α β} {t_ord : t.Ordered} {lowerBound : α} :
    (RciIterator t lowerBound : Iter (Sigma β)).toList =
      t.toList.filter (fun e => (compare e.fst lowerBound).isGE) := by
  simp only [RciIterator]
  have := @Zipper.toList_iter _ _ (Zipper.prependMapGE t lowerBound Zipper.done)
  simp only [Zipper.iter] at this
  simp only [this]
  rw [← Zipper.prepend_pruneLE_eq_prependMapGE]
  . simp only [Zipper.toList_prependMap_eq_append, Zipper.toList, List.append_nil]
    apply Impl.pruneLE_eq_filter
    exact t_ord
  . exact t_ord

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
  . exact ordered

end Rci

section Roi
@[always_inline]
public def RoiIterator [Ord α] (t : Impl α β) (lowerBound : α) : Iter (α := Zipper α β) ((a : α) × β a) :=
  ⟨Zipper.prependMapGT t lowerBound .done⟩

public theorem toList_roiIter {α β} [Ord α] [TransOrd α]
    {t : Impl α β} {t_ord : t.Ordered} {lowerBound : α} :
    (RoiIterator t lowerBound : Iter (Sigma β)).toList =
      t.toList.filter (fun e => (compare e.fst lowerBound).isGT) := by
  simp only [RoiIterator]
  have := @Zipper.toList_iter _ _ (Zipper.prependMapGT t lowerBound .done)
  simp only [Zipper.iter] at this
  rw [this]
  rw [← Zipper.prepend_pruneLT_eq_prependMapGT]
  . simp only [Zipper.toList_prependMap_eq_append, Zipper.toList, List.append_nil]
    apply Impl.pruneLT_eq_filter
    exact t_ord
  . exact t_ord

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
  . exact ordered

end Roi

section Rii

public def RiiIterator (t : Impl α β) : Iter (α := Zipper α β) ((a : α) × β a) :=
  ⟨Zipper.prependMap t .done⟩

public theorem toList_riiIter {α β}
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

end Std.DTreeMap.Internal
