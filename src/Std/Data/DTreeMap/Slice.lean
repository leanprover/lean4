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

section MapIterator
public inductive Zipper (α : Type u) (β : α → Type v) where
  | done
  | cons (k : α) (v : β k) (tree : Internal.Impl α β) (next : Zipper α β)

variable {α : Type u} {β : α → Type v}

public def Zipper.toList : Zipper α β → List ((a : α) × β a)
| .done => []
| .cons k v tree next => ⟨k,v⟩ :: tree.toList ++ next.toList

public def Zipper.keys : Zipper α β → List α
| .done => []
| .cons k _ tree next => k :: tree.keys ++ next.keys

def Zipper.size : Zipper α β → Nat
| .done => 0
| .cons _ _ tree next => 1 + tree.treeSize + next.size

public def Zipper.WF [Ord α] : Zipper α β → Prop
| .done => True
| .cons k _ tree next => tree.keys.all (fun key => (compare key k).isLE) ∧ next.keys.all (fun key => (compare key k).isLE)

public def Zipper.prependMap : Internal.Impl α β → Zipper α β → Zipper α β
  | .leaf, it => it
  | .inner _ k v l r, it => prependMap l (.cons k v r it)

theorem prependMap_WF_inv [Ord α] [TransOrd α] {t : Internal.Impl α β} {wf : Internal.Impl.WF t} {z : Zipper α β} {z_wf : Zipper.WF z} : Zipper.WF (Zipper.prependMap t z) := by
  induction t generalizing z
  case leaf =>
    simp [Zipper.prependMap]
    exact z_wf
  case inner _ k v l r l_ih r_ih =>
    simp [Zipper.prependMap]
    apply l_ih
    . sorry
    . constructor
      sorry
      sorry

public theorem Zipper.prependMap_to_list (t : Internal.Impl α β) (it : Zipper α β) : (Zipper.prependMap t it).toList = t.toList ++ it.toList := by
  induction t generalizing it
  case leaf =>
    simp [prependMap, Internal.Impl.toList_eq_toListModel]
  case inner _ k v l r l_ih r_ih =>
    simp only [Zipper.prependMap]
    specialize l_ih (Zipper.cons k v r it)
    rw [l_ih]
    simp [toList, Internal.Impl.toList_eq_toListModel]

theorem Zipper.prependMap_size (t : Internal.Impl α β) (it : Zipper α β) : (Zipper.prependMap t it).size = t.treeSize + it.size := by
  fun_induction Zipper.prependMap
  case case1 =>
   simp only [Internal.Impl.treeSize, Nat.zero_add]
  case case2 size k v l r it ih =>
    simp only [ih, Zipper.size, Internal.Impl.treeSize, ← Nat.add_assoc, Nat.add_comm]

end MapIterator

section Rxc

public structure RxcIterator (α : Type u) (β : α → Type v) (cmp : α → α → Ordering) where
  iter : Zipper α β
  upper : α

variable {α : Type u} {β : α → Type v}

public def RxcIterator.inBounds {cmp : α → α → Ordering} (it : RxcIterator α β cmp) (k : α) : Bool :=
  (cmp k it.upper).isLE

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

public theorem toList_lemma {it : Iter (α := RxcIterator α β cmp) ((a : α) × β a)} : it.toList = it.internalState.iter.toList.filter (fun e => (cmp e.fst bound).isLE) := by
  unfold Iter.toList
  simp [Iter.toIterM]
  unfold Iter.internalState
  simp [instIteratorCollectRxcIteratorIdSigma]
  sorry

public theorem step_rxcIterator_eq_match {cmp : α → α → Ordering} {it : IterM (α := RxcIterator α β cmp) Id ((a : α) × β a)} :
    it.step = ⟨match it.internalState with
    | { iter := Zipper.done, upper := _ } => IterStep.done
    | { iter := Zipper.cons k v t it, upper := upper } =>
      if (cmp k upper).isLE = true then
        IterStep.yield { internalState := { iter := Zipper.prependMap t it, upper := upper } } ⟨k, v⟩
      else IterStep.done,
    (by simp only [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, RxcIterator.step]; split; all_goals (rename_i heq; simp only [heq]))⟩ := by
  simp [IterM.step, Iterator.step, RxcIterator.step]
  ext
  congr 1

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

def test : DTreeMap.Raw Nat (fun _ => Nat) compare := .ofList [⟨0, 0⟩, ⟨1, 1⟩, ⟨100, 3⟩, ⟨101, 4⟩]

-- RxcIterator α β cmp
public theorem step_iter_ricSlice_eq_match {α β} {cmp : α → α → Ordering} {t : DTreeMap.Raw α β cmp} {a b : α} :
    t[*...=b].iter.step = ⟨match ({ iter := Zipper.prependMap t.inner Zipper.done, upper := b } : RxcIterator α β cmp) with
        | { iter := Zipper.done, upper := upper } => IterStep.done
        | { iter := Zipper.cons k v t it, upper := upper } =>
          if (cmp k upper).isLE = true then
            IterStep.yield { internalState := { iter := Zipper.prependMap t it, upper := upper } } ⟨k, v⟩
          else IterStep.done, (sorry)⟩ := by
  rw [Slice.iter_eq_toIteratorIter]
  simp only [Ric.Sliceable.mkSlice, instSliceableRawRicSlice, RicSlice.Internal.iterM, ToIterator.iter_eq, IterM.toIter, Iter.step]
  rw [step_rxcIterator_eq_match]
  simp only [Iter.toIterM]
  simp only [IterM.Step.toPure, IterStep.mapIterator, Id.run]
  congr
  split
  case h_1 =>
    rename_i heq
    split at heq
    any_goals contradiction
    . rename_i heq2
      simp at heq2
      split at heq
      . simp at heq
        rename_i heq3
        simp [heq3, ← heq.1, heq.2, IterM.toIter]
      . contradiction
  case h_2 =>
    rename_i heq
    split at heq
    any_goals contradiction
    . rename_i heq
      split at heq
      . contradiction
      . contradiction
  case h_3 =>
    rename_i heq
    split at heq
    any_goals trivial
    split at heq
    . contradiction
    . rename_i heq2
      simp [heq2]

public theorem toList_rocSlice_eq_filter_toList {α β} {cmp : α → α → Ordering}
    {t : DTreeMap.Raw α β cmp} (h : t.WF) {bound : α} :
    t[*...=bound].toList = t.toList.filter (fun e => (cmp e.fst bound).isLE) := by
      simp only [Slice.toList_eq_toList_iter]
      rw [Iter.toList_eq_match_step]
      rw [step_iter_ricSlice_eq_match]
      split
      case h_1 x it' out heq =>
        split at heq
        any_goals contradiction
        rename_i x' k v t it upper heq2
        simp at heq2
        split at heq
        any_goals contradiction
        simp at heq
        rename_i isLE
        rename_i t'
        have ⟨heq₁, heq₂⟩ := heq
        rw [← heq₂]
        have := @Zipper.prependMap_to_list α β t'.inner .done
        rw [heq2.1] at this
        simp [Zipper.toList] at this
        rw [← heq₁]
        have toList_lemma := @toList_lemma α β cmp bound { internalState := { iter := Zipper.prependMap t it, upper := upper } }
        simp at toList_lemma
        rw [toList_lemma]
        simp only [Raw.toList]
        rw [← this]
        simp only [List.filter, isLE, heq2.2]
        congr
        simp [Zipper.prependMap_to_list]
      case h_2 =>
        rename_i heq
        split at heq
        any_goals contradiction
        . split at heq
          any_goals contradiction
      case h_3 x heq =>
        split at heq
        case h_1 it upper heq2 =>
          simp at heq2
          unfold Zipper.prependMap at heq2
          split at heq2
          . rename_i eq_empty
            simp only [Raw.toList]
            rw [eq_empty]
            rw [Internal.Impl.toList_eq_toListModel]
            simp only [Internal.Impl.toListModel_leaf, List.filter_nil]
          . rename_i t₁ t₂ _ k v l r heq3
            replace heq2 := heq2.1
            sorry
        case h_2 x' k v t it upper heq2 =>
          split at heq
          . contradiction
          . rename_i t' notLE
            simp at heq2
            have ⟨heq2₁, heq2₂⟩ := heq2
            clear heq2
            have prependMap_to_List := @Zipper.prependMap_to_list α β t'.inner Zipper.done
            simp [heq2₁, Zipper.toList] at prependMap_to_List
            simp only [Raw.toList]
            rw [← prependMap_to_List]
            simp only [List.filter]
            rw [← heq2₂] at notLE
            simp only [notLE]

            sorry
      exact bound

































#eval test[*...=1].toList


end Rxc
end Std.DTreeMap
