/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Init.Data.Iterators.Basic
public import Init.Data.Iterators.Consumers
public import Std.Data.Iterators.Lemmas.Producers.Slice
public import Init.Data.Slice
public import Init.Data.Range.Polymorphic.Basic
public import Std.Data.DTreeMap
public import Std.Data.DTreeMap.Internal.Lemmas


namespace Std.DTreeMap.Internal
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

public def Zipper.prependMapGE [Ord α] (t : Impl α β) (lower_bound : α)
    (it : Zipper α β) : Zipper α β :=
  match t with
  | .leaf => it
  | .inner _ k v l r =>
    match compare lower_bound k with
    | .lt => prependMapGE l lower_bound (Zipper.cons k v r it)
    | .eq => .cons k v r it
    | .gt => prependMapGE r lower_bound it

public def Zipper.prependMapGT [Ord α] (t : Impl α β) (lower_bound : α)
    (it : Zipper α β) : Zipper α β :=
  match t with
  | .leaf => it
  | .inner _ k v l r =>
    match compare lower_bound k with
    | .lt => prependMapGT l lower_bound (Zipper.cons k v r it)
    | .eq => prependMapGT r lower_bound it
    | .gt => prependMapGT r lower_bound it

theorem Zipper.prepend_prune_LE_eq_prependMapGE [Ord α] (t : Impl α β) (ord_t : t.Ordered)
    (z : Zipper α β) (lower_bound : α) :
    z.prependMap (t.prune_LE ord_t lower_bound) = z.prependMapGE t lower_bound := by
  induction t generalizing z
  case leaf =>
    simp only [Impl.prune_LE, Zipper.prependMap, Zipper.prependMapGE]
  case inner _ k v l r l_ih r_ih =>
    simp only [Impl.prune_LE, Zipper.prependMapGE]
    generalize heq : compare lower_bound k = x
    cases x
    case lt =>
      simp only
      apply l_ih
    case eq =>
      simp only [Zipper.prependMap]
    case gt =>
      simp only
      apply r_ih

theorem Zipper.prepend_eq_prependMapGT_self [Ord α] [TransOrd α] (r : Impl α β)
    (z : Zipper α β) (lower_bound : α) (ord_r : r.Ordered)
    (hyp : ∀ e ∈ r.toList, compare lower_bound e.fst = .lt) :
    Zipper.prependMap r z = Zipper.prependMapGT r lower_bound z := by
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

theorem Zipper.prepend_prune_LT_eq_prependMapGT [Ord α] [TransOrd α] (t : Impl α β)
    (ord_t : t.Ordered) (z : Zipper α β) (lower_bound : α) :
    z.prependMap (t.prune_LT ord_t lower_bound) = z.prependMapGT t lower_bound := by
  induction t generalizing z
  case leaf =>
    simp only [Impl.prune_LT, Zipper.prependMap, Zipper.prependMapGT]
  case inner _ k v l r l_ih r_ih =>
    simp only [Impl.prune_LT, Zipper.prependMapGT]
    generalize heq : compare lower_bound k = x
    cases x
    case lt =>
      simp only [Zipper.prependMap]
      apply l_ih
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

public theorem Zipper.prependMap_toList_eq_concat_toList (t : Impl α β)
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

public theorem Zipper.prependMap_done_toList_eq_toList (t : Impl α β) : (Zipper.prependMap t .done).toList = t.toList := by
  simp [Zipper.prependMap_toList_eq_concat_toList, Zipper.toList]

theorem Zipper.prependMap_invariant [Ord α] [TransOrd α] {t : Impl α β}
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
        simp only [Ordered, prependMap_toList_eq_concat_toList] at this
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

theorem Zipper.prependMap_done_invariant [Ord α] [TransOrd α] {t : Impl α β}
    {ord_t : t.Ordered} :
    (Zipper.prependMap t .done).Ordered := by
  apply Zipper.prependMap_invariant
  . exact ord_t
  . simp only [Ordered, toList, List.Pairwise.nil]
  simp only [toList, List.not_mem_nil, false_implies, implies_true]

public theorem Zipper.ordered_of_cons_ordered [Ord α] [TransOrd α] {t : Impl α β}
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

@[always_inline]
public def Zipper.iter (t : Zipper α β) : Iter (α := Zipper α β) ((a : α) × β a) :=
  ⟨t⟩

@[always_inline]
public def Zipper.iter_of_tree (t : Impl α β) : Iter (α := Zipper α β) ((a : α) × β a) :=
  Zipper.iter <| Zipper.done.prependMap t

public theorem Zipper.iter_of_tree_toList_eq_zipper_prependMap_toList (t : Impl α β) :
    (Zipper.iter_of_tree t).internalState.toList = t.toList := by
  unfold iter_of_tree
  unfold iter
  simp only
  simp [prependMap_toList_eq_concat_toList, toList]

public instance {z : Zipper α β} : ToIterator z Id ((a : α) × β a) where
  State := Zipper α β
  iterMInternal := Iter.toIterM <| Zipper.iter z

public theorem Zipper.step_eq_match {it : IterM (α := Zipper α β) Id ((a : α) × β a)} :
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

public theorem Zipper.val_step_Zipper_eq_match {α β}
    {it : Iter (α := Zipper α β) (Sigma β)} :
    it.step.val =
        match it.internalState.iter with
        | ⟨Zipper.done⟩ => IterStep.done
        | ⟨Zipper.cons k v t it'⟩ =>
            IterStep.yield { internalState := Zipper.prependMap t it'  } ⟨k, v⟩
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

public theorem Zipper.toList_Zipper {α β}
    {z : Zipper α β}:
    (⟨z⟩ : Iter (Sigma β)).toList =
      z.toList := by
  rw [Iter.toList_eq_match_step]
  generalize hit : (⟨z⟩ : Iter (Sigma β)).step.val = step
  rw [val_step_Zipper_eq_match] at hit
  simp only at hit
  split at hit <;> rename_i heq
  · simp only [← hit, List.nil_eq]
    cases z
    . rw [Zipper.toList]
    . simp only [Zipper.iter, Iter.mk.injEq, reduceCtorEq] at heq
  . rename_i x k v t it'
    simp only [← hit]
    rw [toList_Zipper]
    . generalize heq2 : Zipper.cons k v t it' = y
      rw [heq2] at heq
      simp only [Zipper.iter, Iter.mk.injEq] at heq
      rw [heq]
      rw [← heq2]
      simp only [Zipper.toList, List.cons_append, List.cons.injEq, true_and]
      rw [Zipper.prependMap_toList_eq_concat_toList]
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

public theorem Zipper.val_step_map_Zipper_eq_match {α β γ} {f : (a : α) × β a → γ}
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

public theorem Zipper.toList_map_Zipper {α β γ} {f : (a : α) × β a → γ}
    {z : Zipper α β}:
    ((⟨z⟩ : Iter (Sigma β)).map f).toList =
      (z.toList).map f := by
  rw [Iter.toList_eq_match_step]
  generalize hit : ((⟨z⟩ : Iter (Sigma β)).map f).step.val = step
  rw [val_step_map_Zipper_eq_match] at hit
  simp only at hit
  split at hit
  case h_1 x heq =>
    simp only [← hit, List.nil_eq]
    cases z
    . simp only [Zipper.toList, List.map_nil]
    . simp only [Zipper.iter, Iter.mk.injEq, reduceCtorEq] at heq
  case h_2 =>
    rename_i x k v t z' heq
    simp only [← hit]
    rw [← toList_Zipper]
    . generalize heq2 : Zipper.cons k v t z' = y
      rw [heq2] at heq
      simp only [Zipper.iter, Iter.mk.injEq] at heq
      rw [heq]
      rw [← heq2]
      conv =>
        rhs
        rw [toList_Zipper]
      simp only [Iter.toList_map, Zipper.toList, List.cons_append, List.map_cons]
      simp only [← Zipper.prependMap_toList_eq_concat_toList, List.cons.injEq, true_and]
      rw [←toList_map_Zipper]
      simp
  termination_by z.size
  decreasing_by
    simp_all
    rename_i k v t z' _ heq
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

public theorem Zipper.iter_of_tree_internal_state_eq {m : Impl α β} :
    (Zipper.iter_of_tree m).internalState = Zipper.prependMap m .done := by
  simp [Zipper.iter_of_tree, Zipper.iter]

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

public instance [Ord α]: Iterator (RxcIterator α β) Id ((a : α) × β a) where
  IsPlausibleStep it step := it.internalState.step = step
  step it := ⟨it.internalState.step, rfl⟩

public instance [Ord α]: IteratorCollect (RxcIterator α β) Id Id := .defaultImplementation

public instance [Ord α]: IteratorCollectPartial (RxcIterator α β) Id Id := .defaultImplementation

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
      rw [toList_rxcIter, Zipper.prependMap_toList_eq_concat_toList]
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

def instProductivenessRelation [Ord α]: ProductivenessRelation (RxcIterator α β) Id where
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

public instance [Ord α]: Iterator (RxoIterator α β) Id ((a : α) × β a) where
  IsPlausibleStep it step := it.internalState.step = step
  step it := ⟨it.internalState.step, rfl⟩

public instance [Ord α]: IteratorCollect (RxoIterator α β) Id Id := .defaultImplementation

public instance [Ord α]: IteratorCollectPartial (RxoIterator α β) Id Id := .defaultImplementation

def RxoIterator.instFinitenessRelation [Ord α]: FinitenessRelation (RxoIterator α β) Id where
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
public instance Rxo.instFinite [Ord α]: Finite (RxoIterator α β) Id :=
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
      rw [toList_rxoIter, Zipper.prependMap_toList_eq_concat_toList]
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

public theorem Ric.correct {α : Type u} {β : α → Type v} [Ord α] [TransOrd α] (t : Impl α β)
    (ordered : t.Ordered) (bound : α) : t[*...=bound].toList = t.toList.filter (fun e => (compare e.fst bound).isLE) := by
  simp only [Ric.Sliceable.mkSlice, Slice.toList_eq_toList_iter, Slice.iter,
    Slice.Internal.iter_eq_toIteratorIter, ToIterator.iter, ToIterator.iterM_eq,
    Iter.toIter_toIterM]
  rw [toList_rxcIter, toList_eq_takeWhile_list]
  . rw [Zipper.prependMap_toList_eq_concat_toList]
    simp [Zipper.toList]
  . exact @Zipper.prependMap_done_invariant _ _ _ _ t ordered

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

public theorem Rio.correct {α : Type u} {β : α → Type v} [Ord α] [TransOrd α] (t : Impl α β)
    (ordered : t.Ordered) (bound : α) : t[*...bound].toList = t.toList.filter (fun e => (compare e.fst bound).isLT) := by
  simp only [Rio.Sliceable.mkSlice, Slice.toList_eq_toList_iter, Slice.iter,
    Slice.Internal.iter_eq_toIteratorIter, ToIterator.iter, ToIterator.iterM_eq,
    Iter.toIter_toIterM]
  rw [toList_rxoIter, toList_eq_takeWhile_list_LT]
  . rw [Zipper.prependMap_toList_eq_concat_toList]
    simp [Zipper.toList]
  . exact @Zipper.prependMap_done_invariant _ _ _ _ t ordered

end Rio

section Rcc

@[always_inline]
public def RccIterator [Ord α] (t : Impl α β) (lower_bound : α) (upper_bound : α)  : Iter (α := RxcIterator α β) ((a : α) × β a) :=
  ⟨RxcIterator.mk (Zipper.prependMapGE t lower_bound .done) upper_bound⟩

public theorem toList_rccIter {α β} [Ord α] [TransOrd α]
    {t : Impl α β} {t_ord : t.Ordered} {lower_bound upper_bound : α} :
    (RccIterator t lower_bound upper_bound : Iter (Sigma β)).toList =
      t.toList.filter (fun e => (compare e.fst lower_bound).isGE ∧ (compare e.fst upper_bound).isLE) := by
  simp only [RccIterator, Bool.decide_and, Bool.decide_eq_true]
  rw [toList_rxcIter, toList_eq_takeWhile_list]
  . conv =>
      rhs
      lhs
      ext x
      rw [Bool.and_comm]
    rw [← List.filter_filter]
    congr 1
    rw [← Zipper.prepend_prune_LE_eq_prependMapGE]
    . rw [Zipper.prependMap_toList_eq_concat_toList, Impl.prune_LE_eq_filter]
      simp only [Zipper.toList, List.append_nil]
    . exact t_ord
  . rw [← Zipper.prepend_prune_LE_eq_prependMapGE]
    . simp only [Zipper.prependMap_toList_eq_concat_toList, Zipper.toList, List.append_nil]
      rw [Impl.prune_LE_eq_filter]
      apply List.Pairwise.filter
      simp only [Impl.Ordered] at t_ord
      rw [Impl.toList_eq_toListModel]
      exact t_ord
    . exact t_ord

public structure RccSliceData (α : Type u) (β : α → Type v) [Ord α] where
  treeMap : Impl α β
  range : Rcc α

public abbrev RccSlice α β [Ord α] := Slice (RccSliceData α β)

public instance {α : Type u} {β : α → Type v} [Ord α] : Rcc.Sliceable (Impl α β) α (RccSlice α β) where
  mkSlice carrier range := ⟨carrier, range⟩

public instance [Ord α] {s : RccSlice α β} : ToIterator s Id ((a : α) × β a) :=
  ToIterator.of (RxcIterator α β) (RccIterator s.1.treeMap s.1.range.lower s.1.range.upper)

public theorem Rcc.correct {α : Type u} {β : α → Type v} [Ord α] [TransOrd α] (t : Impl α β)
    (ordered : t.Ordered) (lower_bound upper_bound : α) : t[lower_bound...=upper_bound].toList = t.toList.filter (fun e => (compare e.fst lower_bound).isGE ∧ (compare e.fst upper_bound).isLE) := by
  simp only [Rcc.Sliceable.mkSlice, Slice.toList_eq_toList_iter, Slice.iter,
    Slice.Internal.iter_eq_toIteratorIter, ToIterator.iter, ToIterator.iterM_eq,
    Iter.toIter_toIterM]
  rw [toList_rccIter]
  . exact ordered

end Rcc

section Rco

@[always_inline]
public def RcoIterator [Ord α] (t : Impl α β) (lower_bound : α) (upper_bound : α)  : Iter (α := RxoIterator α β) ((a : α) × β a) :=
  ⟨RxoIterator.mk (Zipper.prependMapGE t lower_bound .done) upper_bound⟩

public theorem toList_rcoIter {α β} [Ord α] [TransOrd α]
    {t : Impl α β} {t_ord : t.Ordered} {lower_bound upper_bound : α} :
    (RcoIterator t lower_bound upper_bound : Iter (Sigma β)).toList =
      t.toList.filter (fun e => (compare e.fst lower_bound).isGE ∧ (compare e.fst upper_bound).isLT) := by
  simp only [RcoIterator, Bool.decide_and, Bool.decide_eq_true]
  rw [toList_rxoIter, toList_eq_takeWhile_list_LT]
  . conv =>
      rhs
      lhs
      ext x
      rw [Bool.and_comm]
    rw [← List.filter_filter]
    congr 1
    rw [← Zipper.prepend_prune_LE_eq_prependMapGE]
    . rw [Zipper.prependMap_toList_eq_concat_toList, Impl.prune_LE_eq_filter]
      simp only [Zipper.toList, List.append_nil]
    . exact t_ord
  . rw [← Zipper.prepend_prune_LE_eq_prependMapGE]
    . simp only [Zipper.prependMap_toList_eq_concat_toList, Zipper.toList, List.append_nil]
      rw [Impl.prune_LE_eq_filter]
      apply List.Pairwise.filter
      simp only [Impl.Ordered] at t_ord
      rw [Impl.toList_eq_toListModel]
      exact t_ord
    . exact t_ord

public structure RcoSliceData (α : Type u) (β : α → Type v) [Ord α] where
  treeMap : Impl α β
  range : Rco α

public abbrev RcoSlice α β [Ord α] := Slice (RcoSliceData α β)

public instance {α : Type u} {β : α → Type v} [Ord α] : Rco.Sliceable (Impl α β) α (RcoSlice α β) where
  mkSlice carrier range := ⟨carrier, range⟩

public instance [Ord α] {s : RcoSlice α β} : ToIterator s Id ((a : α) × β a) :=
  ToIterator.of (RxoIterator α β) (RcoIterator s.1.treeMap s.1.range.lower s.1.range.upper)

public theorem Rco.correct {α : Type u} {β : α → Type v} [Ord α] [TransOrd α] (t : Impl α β)
    (ordered : t.Ordered) (lower_bound upper_bound : α) : t[lower_bound...<upper_bound].toList = t.toList.filter (fun e => (compare e.fst lower_bound).isGE ∧ (compare e.fst upper_bound).isLT) := by
  simp only [Rco.Sliceable.mkSlice, Slice.toList_eq_toList_iter, Slice.iter,
    Slice.Internal.iter_eq_toIteratorIter, ToIterator.iter, ToIterator.iterM_eq,
    Iter.toIter_toIterM]
  rw [toList_rcoIter]
  . exact ordered

end Rco

section Roo
@[always_inline]
public def RooIterator [Ord α] (t : Impl α β) (lower_bound : α) (upper_bound : α)  : Iter (α := RxoIterator α β) ((a : α) × β a) :=
  ⟨RxoIterator.mk (Zipper.prependMapGT t lower_bound .done) upper_bound⟩

public theorem toList_rooIter {α β} [Ord α] [TransOrd α]
    {t : Impl α β} {t_ord : t.Ordered} {lower_bound upper_bound : α} :
    (RooIterator t lower_bound upper_bound : Iter (Sigma β)).toList =
      t.toList.filter (fun e => (compare e.fst lower_bound).isGT ∧ (compare e.fst upper_bound).isLT) := by
  simp only [RooIterator, Bool.decide_and, Bool.decide_eq_true]
  rw [toList_rxoIter, toList_eq_takeWhile_list_LT]
  . conv =>
      rhs
      lhs
      ext x
      rw [Bool.and_comm]
    rw [← List.filter_filter]
    congr 1
    rw [← Zipper.prepend_prune_LT_eq_prependMapGT]
    . rw [Zipper.prependMap_toList_eq_concat_toList, Impl.prune_LT_eq_filter]
      simp only [Zipper.toList, List.append_nil]
    . exact t_ord
  . rw [← Zipper.prepend_prune_LT_eq_prependMapGT]
    . simp only [Zipper.prependMap_toList_eq_concat_toList, Zipper.toList, List.append_nil]
      rw [Impl.prune_LT_eq_filter]
      apply List.Pairwise.filter
      simp only [Impl.Ordered] at t_ord
      rw [Impl.toList_eq_toListModel]
      exact t_ord
    . exact t_ord

public structure RooSliceData (α : Type u) (β : α → Type v) [Ord α] where
  treeMap : Impl α β
  range : Roo α

public abbrev RooSlice α β [Ord α] := Slice (RooSliceData α β)

public instance {α : Type u} {β : α → Type v} [Ord α] : Roo.Sliceable (Impl α β) α (RooSlice α β) where
  mkSlice carrier range := ⟨carrier, range⟩

public instance [Ord α] {s : RooSlice α β} : ToIterator s Id ((a : α) × β a) :=
  ToIterator.of (RxoIterator α β) (RooIterator s.1.treeMap s.1.range.lower s.1.range.upper)

public theorem Roo.correct {α : Type u} {β : α → Type v} [Ord α] [TransOrd α] (t : Impl α β)
    (ordered : t.Ordered) (lower_bound upper_bound : α) : t[lower_bound<...<upper_bound].toList = t.toList.filter (fun e => (compare e.fst lower_bound).isGT ∧ (compare e.fst upper_bound).isLT) := by
  simp only [Roo.Sliceable.mkSlice, Slice.toList_eq_toList_iter, Slice.iter,
    Slice.Internal.iter_eq_toIteratorIter, ToIterator.iter, ToIterator.iterM_eq,
    Iter.toIter_toIterM]
  rw [toList_rooIter]
  . exact ordered

end Roo

section Roc
@[always_inline]
public def RocIterator [Ord α] (t : Impl α β) (lower_bound : α) (upper_bound : α)  : Iter (α := RxcIterator α β) ((a : α) × β a) :=
  ⟨RxcIterator.mk (Zipper.prependMapGT t lower_bound .done) upper_bound⟩

public theorem toList_rocIter {α β} [Ord α] [TransOrd α]
    {t : Impl α β} {t_ord : t.Ordered} {lower_bound upper_bound : α} :
    (RocIterator t lower_bound upper_bound : Iter (Sigma β)).toList =
      t.toList.filter (fun e => (compare e.fst lower_bound).isGT ∧ (compare e.fst upper_bound).isLE) := by
  simp only [RocIterator, Bool.decide_and, Bool.decide_eq_true]
  rw [toList_rxcIter, toList_eq_takeWhile_list]
  . conv =>
      rhs
      lhs
      ext x
      rw [Bool.and_comm]
    rw [← List.filter_filter]
    congr 1
    rw [← Zipper.prepend_prune_LT_eq_prependMapGT]
    . rw [Zipper.prependMap_toList_eq_concat_toList, Impl.prune_LT_eq_filter]
      simp only [Zipper.toList, List.append_nil]
    . exact t_ord
  . rw [← Zipper.prepend_prune_LT_eq_prependMapGT]
    . simp only [Zipper.prependMap_toList_eq_concat_toList, Zipper.toList, List.append_nil]
      rw [Impl.prune_LT_eq_filter]
      apply List.Pairwise.filter
      simp only [Impl.Ordered] at t_ord
      rw [Impl.toList_eq_toListModel]
      exact t_ord
    . exact t_ord

public structure RocSliceData (α : Type u) (β : α → Type v) [Ord α] where
  treeMap : Impl α β
  range : Roc α

public abbrev RocSlice α β [Ord α] := Slice (RocSliceData α β)

public instance {α : Type u} {β : α → Type v} [Ord α] : Roc.Sliceable (Impl α β) α (RocSlice α β) where
  mkSlice carrier range := ⟨carrier, range⟩

public instance [Ord α] {s : RocSlice α β} : ToIterator s Id ((a : α) × β a) :=
  ToIterator.of (RxcIterator α β) (RocIterator s.1.treeMap s.1.range.lower s.1.range.upper)

public theorem Roc.correct {α : Type u} {β : α → Type v} [Ord α] [TransOrd α] (t : Impl α β)
    (ordered : t.Ordered) (lower_bound upper_bound : α) : t[lower_bound<...=upper_bound].toList = t.toList.filter (fun e => (compare e.fst lower_bound).isGT ∧ (compare e.fst upper_bound).isLE) := by
  simp only [Roc.Sliceable.mkSlice, Slice.toList_eq_toList_iter, Slice.iter,
    Slice.Internal.iter_eq_toIteratorIter, ToIterator.iter, ToIterator.iterM_eq,
    Iter.toIter_toIterM]
  rw [toList_rocIter]
  . exact ordered

end Roc

section Rci
@[always_inline]
public def RciIterator [Ord α] (t : Impl α β) (lower_bound : α) : Iter (α := Zipper α β) ((a : α) × β a) :=
  ⟨Zipper.prependMapGE t lower_bound .done⟩

public theorem toList_rciIter {α β} [Ord α] [TransOrd α]
    {t : Impl α β} {t_ord : t.Ordered} {lower_bound : α} :
    (RciIterator t lower_bound : Iter (Sigma β)).toList =
      t.toList.filter (fun e => (compare e.fst lower_bound).isGE) := by
  simp only [RciIterator]
  simp only [Zipper.toList_Zipper]
  rw [← Zipper.prepend_prune_LE_eq_prependMapGE]
  simp only [Zipper.prependMap_toList_eq_concat_toList, Zipper.toList, List.append_nil]
  apply Impl.prune_LE_eq_filter
  exact t_ord

public structure RciSliceData (α : Type u) (β : α → Type v) [Ord α] where
  treeMap : Impl α β
  range : Rci α

public abbrev RciSlice α β [Ord α] := Slice (RciSliceData α β)

public instance {α : Type u} {β : α → Type v} [Ord α] : Rci.Sliceable (Impl α β) α (RciSlice α β) where
  mkSlice carrier range := ⟨carrier, range⟩

public instance [Ord α] {s : RciSlice α β} : ToIterator s Id ((a : α) × β a) :=
  ToIterator.of (Zipper α β) (RciIterator s.1.treeMap s.1.range.lower)

public theorem Rci.correct {α : Type u} {β : α → Type v} [Ord α] [TransOrd α] (t : Impl α β)
    (ordered : t.Ordered) (lower_bound : α) : t[lower_bound...*].toList = t.toList.filter (fun e => (compare e.fst lower_bound).isGE) := by
  simp only [Rci.Sliceable.mkSlice, Slice.toList_eq_toList_iter, Slice.iter,
    Slice.Internal.iter_eq_toIteratorIter, ToIterator.iter, ToIterator.iterM_eq,
    Iter.toIter_toIterM]
  rw [toList_rciIter]
  . exact ordered

end Rci

section Roi
@[always_inline]
public def RoiIterator [Ord α] (t : Impl α β) (lower_bound : α) : Iter (α := Zipper α β) ((a : α) × β a) :=
  ⟨Zipper.prependMapGT t lower_bound .done⟩

public theorem toList_roiIter {α β} [Ord α] [TransOrd α]
    {t : Impl α β} {t_ord : t.Ordered} {lower_bound : α} :
    (RoiIterator t lower_bound : Iter (Sigma β)).toList =
      t.toList.filter (fun e => (compare e.fst lower_bound).isGT) := by
  simp only [RoiIterator]
  simp only [Zipper.toList_Zipper]
  rw [← Zipper.prepend_prune_LT_eq_prependMapGT]
  simp only [Zipper.prependMap_toList_eq_concat_toList, Zipper.toList, List.append_nil]
  apply Impl.prune_LT_eq_filter
  exact t_ord

public structure RoiSliceData (α : Type u) (β : α → Type v) [Ord α] where
  treeMap : Impl α β
  range : Roi α

public abbrev RoiSlice α β [Ord α] := Slice (RoiSliceData α β)

public instance {α : Type u} {β : α → Type v} [Ord α] : Roi.Sliceable (Impl α β) α (RoiSlice α β) where
  mkSlice carrier range := ⟨carrier, range⟩

public instance [Ord α] {s : RoiSlice α β} : ToIterator s Id ((a : α) × β a) :=
  ToIterator.of (Zipper α β) (RoiIterator s.1.treeMap s.1.range.lower)

public theorem Roi.correct {α : Type u} {β : α → Type v} [Ord α] [TransOrd α] (t : Impl α β)
    (ordered : t.Ordered) (lower_bound : α) : t[lower_bound<...*].toList = t.toList.filter (fun e => (compare e.fst lower_bound).isGT) := by
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
  simp only [Zipper.toList_Zipper]
  simp only [Zipper.prependMap_toList_eq_concat_toList, Zipper.toList, List.append_nil]

public structure RiiSliceData (α : Type u) (β : α → Type v) where
  treeMap : Impl α β
  range : Rii α

public abbrev RiiSlice α β := Slice (RiiSliceData α β)

public instance {α : Type u} {β : α → Type v} : Rii.Sliceable (Impl α β) α (RiiSlice α β) where
  mkSlice carrier range := ⟨carrier, range⟩

public instance {s : RiiSlice α β} : ToIterator s Id ((a : α) × β a) :=
  ToIterator.of (Zipper α β) (RiiIterator s.1.treeMap)

public theorem Rii.correct {α : Type u} {β : α → Type v} (t : Impl α β) : t[*...*].toList = t.toList := by
  simp only [Rii.Sliceable.mkSlice, Slice.toList_eq_toList_iter, Slice.iter,
    Slice.Internal.iter_eq_toIteratorIter, ToIterator.iter, ToIterator.iterM_eq,
    Iter.toIter_toIterM]
  rw [toList_riiIter]

end Rii

end Std.DTreeMap.Internal
