/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Rozowski
-/
module

prelude
public import Init.Data.Iterators.Basic
public import Init.Data.Iterators.Consumers
public import Std.Data.Iterators.Lemmas.Producers.Slice
public import Init.Data.Slice
public import Init.Data.Range.Polymorphic.Basic
public import Std.Data.DTreeMap

namespace Std.DTreeMap
open Std.Iterators

public def Internal.Impl.treeSize : Internal.Impl α β → Nat
| .leaf => 0
| .inner _ _ _ l r => 1 + l.treeSize + treeSize r

public def Internal.Impl.prune_LE {α β} [Ord α] (t : Internal.Impl α β) (ord_t : t.Ordered) (lower_bound : α) : Internal.Impl α β :=
  match t with
  | .leaf => .leaf
  | .inner sz k v l r =>
    match compare lower_bound k with
    | .lt => .inner sz k v (l.prune_LE (Internal.Impl.Ordered.left ord_t) lower_bound) r
    | .eq => .inner sz k v .leaf r
    | .gt => r.prune_LE (Internal.Impl.Ordered.right ord_t) lower_bound

public def Internal.Impl.prune_LT {α β} [Ord α] (t : Internal.Impl α β) (ord_t : t.Ordered) (lower_bound : α) : Internal.Impl α β :=
  match t with
  | .leaf => .leaf
  | .inner sz k v l r =>
    match compare lower_bound k with
    | .lt => .inner sz k v (l.prune_LT (Internal.Impl.Ordered.left ord_t) lower_bound) r
    | .eq => r
    | .gt => r.prune_LT (Internal.Impl.Ordered.right ord_t) lower_bound

theorem Internal.Impl.prune_LE_filter {α β} [Ord α] [TransOrd α] (t : Internal.Impl α β) (ord_t : t.Ordered) (lower_bound : α) :
    (t.prune_LE ord_t lower_bound).toList = t.toList.filter (fun e => (compare e.fst lower_bound).isGE) := by
  induction t
  case leaf =>
    simp only [prune_LE, toList_eq_toListModel, toListModel_leaf, List.filter_nil]
  case inner _ k v l r l_ih r_ih =>
    simp only [prune_LE, toList_eq_toListModel, toListModel_inner, List.filter_append]
    generalize heq : compare lower_bound k = x
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
      suffices new_goal : List.filter (fun e => (compare e.fst lower_bound).isGE) l.toListModel = [] from by
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
      simp [heq]
      suffices new_goal : List.filter (fun e => (compare e.fst lower_bound).isGE) l.toListModel = [] from by
        simp [new_goal]
        simp [toList_eq_toListModel] at r_ih
        apply r_ih
      rw [List.filter_eq_nil_iff]
      intro a mem
      simp only [Bool.not_eq_true, Ordering.isGE_eq_false]
      exact TransCmp.lt_trans (Internal.Impl.Ordered.compare_left ord_t mem) heq

theorem Internal.Impl.prune_LT_filter {α β} [Ord α] [TransOrd α] (t : Internal.Impl α β) (ord_t : t.Ordered) (lower_bound : α) :
    (t.prune_LT ord_t lower_bound).toList = t.toList.filter (fun e => (compare e.fst lower_bound).isGT) := by
  induction t
  case leaf =>
    simp [toList_eq_toListModel, prune_LT]
  case inner _ k v l r l_ih r_ih =>
    simp [toList_eq_toListModel, prune_LT]
    generalize heq : compare lower_bound k = x
    cases x
    case lt =>
      simp
      specialize l_ih (Internal.Impl.Ordered.left ord_t)
      rw [toList_eq_toListModel] at l_ih
      simp [l_ih, toList_eq_toListModel]
      simp [List.filter]
      rw [OrientedOrd.eq_swap] at heq
      rw [Ordering.swap_eq_lt] at heq
      simp [heq]
      symm
      apply List.filter_eq_self.2
      intro a mem
      simp
      apply TransCmp.gt_trans ?_ heq
      rw [OrientedOrd.eq_swap]
      rw [Ordering.swap_eq_gt]
      exact Internal.Impl.Ordered.compare_right ord_t mem
    case eq =>
      simp [List.filter]
      rw [OrientedCmp.eq_comm] at heq
      simp [heq]
      suffices new_goal : List.filter (fun e => (compare e.fst lower_bound).isGT) l.toListModel = [] ∧
          List.filter (fun e => (compare e.fst lower_bound).isGT) r.toListModel = r.toListModel from by
        simp [new_goal]
      apply And.intro
      . rw [List.filter_eq_nil_iff]
        intro a mem
        simp [← Ordering.isLE_iff_ne_gt]
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
      simp [List.filter]
      rw [OrientedOrd.eq_swap] at heq
      rw [Ordering.swap_eq_gt] at heq
      simp [heq]
      specialize r_ih (Ordered.right ord_t)
      rw [toList_eq_toListModel] at r_ih
      simp [r_ih, toList_eq_toListModel]
      intro a mem
      rw [← Ordering.isLE_iff_ne_gt]
      apply Ordering.isLE_of_eq_lt
      exact TransCmp.lt_trans (Internal.Impl.Ordered.compare_left ord_t mem) heq

section MapIterator
public inductive Zipper (α : Type u) (β : α → Type v) where
  | done
  | cons (k : α) (v : β k) (tree : Internal.Impl α β) (next : Zipper α β)

variable {α : Type u} {β : α → Type v}

public def Zipper.toList : Zipper α β → List ((a : α) × β a)
| .done => []
| .cons k v tree next => ⟨k,v⟩ :: tree.toList ++ next.toList

public def Zipper.Ordered [Ord α] (t : Zipper α β) : Prop :=
  t.toList.Pairwise (fun a b => compare a.1 b.1 = .lt)

def Zipper.size : Zipper α β → Nat
| .done => 0
| .cons _ _ tree next => 1 + tree.treeSize + next.size

public def Zipper.prependMap : Internal.Impl α β → Zipper α β → Zipper α β
  | .leaf, it => it
  | .inner _ k v l r, it => prependMap l (.cons k v r it)

def Zipper.prependMapGE [Ord α] (t : Internal.Impl α β) (lower_bound : α) (it : Zipper α β) : Zipper α β :=
  match t with
  | .leaf => it
  | .inner _ k v l r =>
    match compare lower_bound k with
    | .lt => prependMapGE l lower_bound (Zipper.cons k v r it)
    | .eq => .cons k v r it
    | .gt => prependMapGE r lower_bound it

def Zipper.prependMapGT [Ord α] (t : Internal.Impl α β) (lower_bound : α) (it : Zipper α β) : Zipper α β :=
  match t with
  | .leaf => it
  | .inner _ k v l r =>
    match compare lower_bound k with
    | .lt => prependMapGT l lower_bound (Zipper.cons k v r it)
    | .eq => prependMapGT r lower_bound it
    | .gt => prependMapGT r lower_bound it

theorem prepend_eq_prependGE [Ord α] (t : Internal.Impl α β) (ord_t : t.Ordered) (z : Zipper α β) (lower_bound : α) :
    z.prependMap (t.prune_LE ord_t lower_bound) = z.prependMapGE t lower_bound := by
  induction t generalizing z
  case leaf =>
    simp [Internal.Impl.prune_LE]
    simp [Zipper.prependMap]
    simp [Zipper.prependMapGE]
  case inner _ k v l r l_ih r_ih =>
    simp [Zipper.prependMapGE]
    simp [Internal.Impl.prune_LE]
    generalize heq : compare lower_bound k = x
    cases x
    case lt =>
      simp
      apply l_ih
    case eq =>
      simp [Zipper.prependMap]
    case gt =>
      simp
      apply r_ih

theorem prepend_eq_prependGT_self [Ord α] [TransOrd α] (r : Internal.Impl α β)
    (z : Zipper α β) (lower_bound : α) (ord_r : r.Ordered)
    (hyp : ∀ e ∈ r.toList, compare lower_bound e.fst = .lt) :
    Zipper.prependMap r z = Zipper.prependMapGT r lower_bound z := by
  induction r generalizing z
  case leaf =>
    trivial
  case inner _ k v l r l_ih r_ih =>
    simp [Zipper.prependMap]
    simp [Zipper.prependMapGT]
    have hyp' := hyp ⟨k,v⟩ (by simp [Internal.Impl.toList_eq_toListModel])
    simp at hyp'
    simp [hyp']
    apply l_ih
    . exact (Internal.Impl.Ordered.left ord_r)
    . intro e mem
      apply hyp e
      simp [Internal.Impl.toList_eq_toListModel]
      apply Or.inl
      . rw [Internal.Impl.toList_eq_toListModel] at mem
        exact mem

theorem prepend_eq_prependGT [Ord α] [TransOrd α] (t : Internal.Impl α β) (ord_t : t.Ordered) (z : Zipper α β) (lower_bound : α) :
    z.prependMap (t.prune_LT ord_t lower_bound) = z.prependMapGT t lower_bound := by
  induction t generalizing z
  case leaf =>
    simp [Internal.Impl.prune_LT]
    simp [Zipper.prependMap]
    simp [Zipper.prependMapGT]
  case inner _ k v l r l_ih r_ih =>
    simp [Zipper.prependMapGT]
    simp [Internal.Impl.prune_LT]
    generalize heq : compare lower_bound k = x
    cases x
    case lt =>
      simp [Zipper.prependMap]
      apply l_ih
    case eq =>
      simp only
      apply prepend_eq_prependGT_self
      . exact Internal.Impl.Ordered.right ord_t
      . intro e mem
        apply TransCmp.lt_of_eq_of_lt heq
        apply Internal.Impl.Ordered.compare_right ord_t
        rw [← Internal.Impl.toList_eq_toListModel]
        exact mem
    case gt =>
      simp
      apply r_ih

public theorem Zipper.prependMap_to_list (t : Internal.Impl α β) (it : Zipper α β) : (Zipper.prependMap t it).toList = t.toList ++ it.toList := by
  induction t generalizing it
  case leaf =>
    simp [prependMap, Internal.Impl.toList_eq_toListModel]
  case inner _ k v l r l_ih r_ih =>
    simp only [Zipper.prependMap]
    specialize l_ih (Zipper.cons k v r it)
    rw [l_ih]
    simp [toList, Internal.Impl.toList_eq_toListModel]

theorem Zipper.prependMap_invariant [Ord α] [TransOrd α] {t : Internal.Impl α β}
    {ord_t : t.Ordered} {z : Zipper α β} {ord_z : z.Ordered}
    (hyp : ∀ k ∈ z.toList, ∀ k' ∈ t.toListModel, compare k'.1 k.1 = .lt ) :
    (Zipper.prependMap t z).Ordered := by
  induction t generalizing z
  case leaf =>
    simp [Zipper.prependMap]
    exact ord_z
  case inner _ k v l r l_ih r_ih =>
    simp [prependMap]
    apply l_ih
    . exact Internal.Impl.Ordered.left ord_t
    . simp [Zipper.Ordered]
      simp only [Zipper.toList]
      simp
      apply And.intro
      . intro a hyp
        cases hyp
        . rename_i in_r
          rw [Internal.Impl.toList_eq_toListModel] at in_r
          exact @Internal.Impl.Ordered.compare_right α β _ _ k v l r ord_t a in_r
        . rename_i in_r
          specialize hyp a in_r ⟨k,v⟩
          simp at hyp
          exact hyp
      . have := @r_ih (Internal.Impl.Ordered.right ord_t) z ord_z
        simp [Zipper.Ordered] at this
        simp [Zipper.prependMap_to_list] at this
        . apply this
          intro k₁ mem₁ k₂ mem₂
          specialize hyp k₁ mem₁ k₂ (by simp [mem₂])
          exact hyp
    . intro k₁ mem₁ k₂ mem₂
      simp only [toList, List.cons_append, List.mem_cons, List.mem_append] at mem₁
      apply Or.elim mem₁
      . intro eq_key
        rw [eq_key]
        exact Internal.Impl.Ordered.compare_left ord_t mem₂
      . intro hyp₂
        apply Or.elim hyp₂
        . intro in_r
          apply TransCmp.lt_trans
          . exact Internal.Impl.Ordered.compare_left ord_t mem₂
          . rw [Internal.Impl.toList_eq_toListModel] at in_r
            exact Internal.Impl.Ordered.compare_right ord_t in_r
        . intro in_z
          apply hyp k₁ in_z k₂
          simp [mem₂]

theorem Zipper.prependMap_done_invariant [Ord α] [TransOrd α] {t : Internal.Impl α β}
    {ord_t : t.Ordered} :
    (Zipper.prependMap t .done).Ordered := by
  apply Zipper.prependMap_invariant
  . exact ord_t
  . simp [Ordered, Zipper.toList]
  simp [Zipper.toList]

public theorem Zipper.ordered_of_cons_ordered [Ord α] [TransOrd α] {t : Internal.Impl α β}
    {z : Zipper α β} : (Zipper.cons k v t z).Ordered → z.Ordered := by
  intro hyp
  simp only [Zipper.Ordered, Zipper.toList] at hyp
  simp [Zipper.Ordered]
  exact List.Pairwise.sublist (List.sublist_append_right (⟨k, v⟩ :: t.toList) z.toList) hyp

theorem Zipper.prependMap_size (t : Internal.Impl α β) (it : Zipper α β) : (Zipper.prependMap t it).size = t.treeSize + it.size := by
  fun_induction Zipper.prependMap
  case case1 =>
   simp only [Internal.Impl.treeSize, Nat.zero_add]
  case case2 size k v l r it ih =>
    simp only [ih, Zipper.size, Internal.Impl.treeSize, ← Nat.add_assoc, Nat.add_comm]

end MapIterator

section ZipperIterator
variable {α : Type u} {β : α → Type v}

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
      simp [Zipper.step] at h'
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

@[always_inline]
public def Zipper.iter (t : Zipper α β) : Iter (α := Zipper α β) ((a : α) × β a) :=
  ⟨t⟩

@[always_inline]
public def Zipper.iter_of_tree (t : Internal.Impl α β) : Iter (α := Zipper α β) ((a : α) × β a) :=
  Zipper.iter <| Zipper.done.prependMap t

public instance {z : Zipper α β} : ToIterator z Id ((a : α) × β a) where
  State := Zipper α β
  iterMInternal := Iter.toIterM <| Zipper.iter z

def test : (DTreeMap.Raw Nat (fun _ => Nat) compare) := .ofList [⟨0, 0⟩, ⟨1, 1⟩, ⟨100, 3⟩, ⟨101, 4⟩, ⟨102, 4⟩, ⟨103, 4⟩]

#eval! (Zipper.iter_of_tree (test.inner.prune_LT sorry 1)).toList
#eval (Zipper.iter (Zipper.prependMapGT test.inner 1 .done)).toList

public theorem step_Zipper_eq_match {it : IterM (α := Zipper α β) Id ((a : α) × β a)} :
    it.step = ⟨match it.internalState.iter with
    | ⟨Zipper.done⟩ => IterStep.done
    | ⟨Zipper.cons k v t z⟩ => IterStep.yield { internalState := Zipper.prependMap t z } ⟨k, v⟩,
    (by
      simp only [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, Zipper.step]; split; all_goals (rename_i heq; simp [heq, Zipper.iter]))⟩ := by
  simp [IterM.step, Iterator.step, Zipper.step]
  ext
  congr 1
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

public theorem val_step_Zipper_eq_match {α β}
    {it : Iter (α := Zipper α β) (Sigma β)} :
    it.step.val =
        match it.internalState.iter with
        | ⟨Zipper.done⟩ => IterStep.done
        | ⟨Zipper.cons k v t it'⟩ =>
            IterStep.yield { internalState := Zipper.prependMap t it'  } ⟨k, v⟩
        := by
  rcases it with ⟨z, upper⟩
  rw [Iter.step]
  rw [step_Zipper_eq_match]
  simp only [Iter.toIterM]
  split
  · simp [Zipper.iter, IterM.Step.toPure, IterStep.mapIterator, Id.run]
  · rename_i heq
    simp [Zipper.iter] at heq
  . split
    case h_1 =>
      rename_i heq
      simp [Zipper.iter] at heq
    case h_2 k v tree next x k v t it' heq =>
      simp only [Zipper.iter] at heq
      injections
      rename_i k_eq v_eq tree_eq next_eq
      simp [Iter.step, Iter.toIterM, IterM.step, Id.run, Iterator.step, Zipper.step, IterM.toIter]
      simp_all

public theorem toList_Zipper {α β}
    {z : Zipper α β}:
    (⟨z⟩ : Iter (Sigma β)).toList =
      z.toList := by
  rw [Iter.toList_eq_match_step]
  generalize hit : (⟨z⟩ : Iter (Sigma β)).step.val = step
  rw [val_step_Zipper_eq_match] at hit
  simp only at hit
  split at hit <;> rename_i heq
  · simp [← hit]
    cases z
    . simp [Zipper.toList]
    . simp [Zipper.iter] at heq
  . rename_i x k v t it'
    simp [← hit]
    rw [toList_Zipper]
    . generalize heq2 : Zipper.cons k v t it' = y
      rw [heq2] at heq
      simp [Zipper.iter] at heq
      rw [heq]
      rw [← heq2]
      simp [Zipper.toList]
      rw [Zipper.prependMap_to_list]
termination_by z.size
decreasing_by
  simp_all
  rename_i t _ _ heq
  simp [Zipper.iter] at heq
  rw [heq]
  simp [Zipper.size]
  induction t
  case leaf =>
    simp [Zipper.prependMap]
    simp [Internal.Impl.treeSize]
  case inner =>
    rw [Zipper.prependMap_size]
    simp [Internal.Impl.treeSize]
end ZipperIterator
section Rxc

public structure RxcIterator (α : Type u) (β : α → Type v) (cmp : α → α → Ordering) where
  iter : Zipper α β
  upper : α

variable {α : Type u} {β : α → Type v}

public def RxcIterator.step {cmp : α → α → Ordering} : RxcIterator α β cmp → IterStep (IterM (α := RxcIterator α β cmp) Id ((a : α) × β a)) ((a : α) × β a)
  | ⟨.done, _⟩ => .done
  | ⟨.cons k v t it, upper⟩ =>
    if (cmp k upper).isLE then
      .yield ⟨it.prependMap t, upper⟩ ⟨k, v⟩
    else
      .done

public instance : Iterator (RxcIterator α β cmp) Id ((a : α) × β a) where
  IsPlausibleStep it step := it.internalState.step = step
  step it := ⟨it.internalState.step, rfl⟩

public instance : IteratorCollect (RxcIterator α β cmp) Id Id := .defaultImplementation

public instance : IteratorCollectPartial (RxcIterator α β cmp) Id Id := .defaultImplementation

def instFinitenessRelation : FinitenessRelation (RxcIterator α β cmp) Id where
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
      simp [RxcIterator.step] at h'
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
public instance instFinite : Finite (RxcIterator α β cmp) Id :=
  .of_finitenessRelation instFinitenessRelation

public theorem step_rxcIterator_eq_match {cmp : α → α → Ordering} {it : IterM (α := RxcIterator α β cmp) Id ((a : α) × β a)} :
    it.step = ⟨match it.internalState.iter with
    | Zipper.done => IterStep.done
    | Zipper.cons k v t z =>
      if (cmp k it.internalState.upper).isLE = true then
        IterStep.yield { internalState := { iter := Zipper.prependMap t z, upper := it.internalState.upper } } ⟨k, v⟩
      else IterStep.done,
    (by simp only [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, RxcIterator.step]; split; all_goals (rename_i heq; simp only [heq]))⟩ := by
  simp [IterM.step, Iterator.step, RxcIterator.step]
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

public structure RicSliceData (α : Type u) (β : α → Type v) (cmp : α → α → Ordering := by exact compare) where
  treeMap : DTreeMap.Raw α β cmp
  range : Ric α

public abbrev RicSlice α β cmp := Slice (RicSliceData α β cmp)

public instance : Ric.Sliceable (DTreeMap.Raw α β cmp) α (RicSlice α β cmp) where
  mkSlice carrier range := ⟨carrier, range⟩

@[always_inline]
public def RicSlice.Internal.iterM (s : RicSlice α β cmp) : IterM (α := RxcIterator α β cmp) Id ((a : α) × β a) :=
  ⟨⟨Zipper.done.prependMap s.1.treeMap.inner, s.1.range.upper⟩⟩

public instance {s : RicSlice α β cmp} : ToIterator s Id ((a : α) × β a) where
  State := RxcIterator α β cmp
  iterMInternal := RicSlice.Internal.iterM s

public theorem val_step_rxcIterator_eq_match {α β} [Ord α]
    {it : Iter (α := RxcIterator α β compare) (Sigma β)} :
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
  · simp [IterM.Step.toPure, IterStep.mapIterator, Id.run]
  · split <;> simp [IterM.Step.toPure, IterStep.mapIterator, Id.run, IterM.toIter]

public theorem toList_rxcIter {α β} [Ord α]
    {z : Zipper α β} {bound : α} :
    (⟨RxcIterator.mk (cmp := compare) z bound⟩ : Iter (Sigma β)).toList =
      z.toList.takeWhile (fun e => (compare e.fst bound).isLE) := by
  rw [Iter.toList_eq_match_step]
  generalize hit : (⟨RxcIterator.mk (cmp := compare) z bound⟩ : Iter (Sigma β)).step.val = step
  rw [val_step_rxcIterator_eq_match] at hit
  simp only at hit
  split at hit <;> rename_i heq
  · simp [← hit, Zipper.toList]
  · split at hit
    · simp [← hit, Zipper.toList]
      rw [List.takeWhile_cons_of_pos ‹_›]
      simp
      rw [toList_rxcIter, Zipper.prependMap_to_list]
    · simp [← hit, Zipper.toList]
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
      simp [List.filter, List.takeWhile]
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
  simp [Zipper.Ordered] at z_ord
  apply toList_eq_takeWhile_list
  exact z_ord
end Rxc

section Rcx

@[always_inline]
public def Rcx [Ord α] (t : Internal.Impl α β) (lower_bound : α) : Iter (α := Zipper α β) ((a : α) × β a) :=
  ⟨Zipper.prependMapGE t lower_bound .done⟩

public theorem toList_rcxIter {α β} [Ord α] [TransOrd α]
    {t : Internal.Impl α β} {t_ord : t.Ordered} {lower_bound : α} :
    (Rcx t lower_bound : Iter (Sigma β)).toList =
      t.toList.filter (fun e => (compare e.fst lower_bound).isGE) := by
  simp [Rcx]
  simp [toList_Zipper]
  rw [← prepend_eq_prependGE]
  simp [Zipper.prependMap_to_list, Zipper.toList]
  apply Internal.Impl.prune_LE_filter
  exact t_ord

end Rcx

section Rcc

@[always_inline]

public def Rcc [Ord α] (t : Internal.Impl α β) (lower_bound : α) (upper_bound : α)  : Iter (α := RxcIterator α β compare) ((a : α) × β a) :=
  ⟨RxcIterator.mk (Zipper.prependMapGE t lower_bound .done) upper_bound⟩

public theorem toList_rccIter {α β} [Ord α] [TransOrd α]
    {t : Internal.Impl α β} {t_ord : t.Ordered} {lower_bound upper_bound : α} :
    (Rcc t lower_bound upper_bound : Iter (Sigma β)).toList =
      t.toList.filter (fun e => (compare e.fst lower_bound).isGE ∧ (compare e.fst upper_bound).isLE) := by
  simp [Rcc]
  rw [toList_rxcIter]
  rw [toList_eq_takeWhile_list]
  . conv =>
      rhs
      lhs
      ext x
      rw [Bool.and_comm]
    rw [← List.filter_filter]
    congr 1
    rw [← prepend_eq_prependGE]
    . rw [Zipper.prependMap_to_list]
      rw [Internal.Impl.prune_LE_filter]
      simp [Zipper.toList]
    . exact t_ord
  . rw [← prepend_eq_prependGE]
    . simp [Zipper.prependMap_to_list]
      simp [Zipper.toList]
      rw [Internal.Impl.prune_LE_filter]
      apply List.Pairwise.filter
      simp [Internal.Impl.Ordered] at t_ord
      rw [Internal.Impl.toList_eq_toListModel]
      exact t_ord
    . exact t_ord

end Rcc

end Std.DTreeMap
