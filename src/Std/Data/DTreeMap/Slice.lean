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

-- Zipper-based iterator for tree maps
inductive MapIterator (α : Type u) (β : α → Type v) where
  | done
  | cons (k : α) (v : β k) (tree : Internal.Impl α β) (next : MapIterator α β)

def MapIterator.toList : MapIterator α β → List ((a : α) × β a)
| .done => []
| .cons k v tree next => ⟨k,v⟩ :: tree.toList ++ next.toList

def treeSize : Internal.Impl α β → Nat
| .leaf => 0
| .inner _ _ _ l r => 1 + treeSize l + treeSize r

def MapIterator.size : MapIterator α β → Nat
| .done => 0
| .cons _ _ tree next => 1 + treeSize (tree) + next.size

def MapIterator.prependMap : Internal.Impl α β → MapIterator α β → MapIterator α β
  | .leaf, it => it
  | .inner _ k v l r, it => prependMap l (.cons k v r it)

def prependMap_to_list (t : Internal.Impl α β) (it : MapIterator α β) : (MapIterator.prependMap t it).toList = t.toList ++ it.toList := by
  induction t generalizing it
  case leaf =>
    simp [MapIterator.prependMap, Internal.Impl.toList_eq_toListModel]
  case inner _ k v l r l_ih r_ih =>
    simp only [MapIterator.prependMap]
    specialize l_ih (MapIterator.cons k v r it)
    rw [l_ih]
    simp [MapIterator.toList, Internal.Impl.toList_eq_toListModel]

variable (α : Type u) (β : α → Type v)
theorem prependMap_size  (t : Internal.Impl α β) (it : MapIterator α β) : (MapIterator.prependMap t it).size = treeSize t + it.size := by
  fun_induction MapIterator.prependMap
  case case1 =>
   simp only [treeSize, Nat.zero_add]
  case case2 size k v l r it ih =>
    simp only [ih, MapIterator.size, treeSize, ← Nat.add_assoc, Nat.add_comm]

structure RxcIterator (cmp : α → α → Ordering) where
  iter : MapIterator α β
  upper : α

def RxcIterator.inBounds {cmp : α → α → Ordering} (it : RxcIterator α β cmp) (k : α) : Bool :=
  (cmp k it.upper).isLE

def RxcIterator.step {cmp : α → α → Ordering} : RxcIterator α β cmp → IterStep (IterM (α := RxcIterator α β cmp) Id ((a : α) × β a)) ((a : α) × β a)
  | ⟨.done, _⟩ => .done
  | ⟨.cons k v t it, upper⟩ =>
    if (cmp k upper).isLE then
      .yield ⟨it.prependMap t, upper⟩ ⟨k, v⟩
    else
      .done

instance : Iterator (RxcIterator α β cmp) Id ((a : α) × β a) where
  IsPlausibleStep it step := it.internalState.step = step
  step it := ⟨it.internalState.step, rfl⟩

def RxC_finite : FinitenessRelation (RxcIterator α β cmp) Id where
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
          simp only [h2, ← h'.1, prependMap_size, MapIterator.size, Nat.add_lt_add_iff_right,
            Nat.lt_add_left_iff_pos, Nat.lt_add_one]

instance instFinite [TransCmp cmp] : Finite (RxcIterator α β cmp) Id :=
  .of_finitenessRelation (RxC_finite α β)

instance : IteratorCollect (RxcIterator α β cmp) Id Id := .defaultImplementation

instance : IteratorCollectPartial (RxcIterator α β cmp) Id Id := .defaultImplementation

def test : Internal.Impl Nat fun _ => Nat :=
  .ofList [⟨1, 2⟩, ⟨5, 4⟩, ⟨3, 1⟩, ⟨2, 8⟩, ⟨7, 9⟩, ⟨10, 5⟩]

def iterLE (t : Internal.Impl α β) (comp : α → α → Ordering) (bound : α) : IterM (α := RxcIterator α β comp) Id ((a : α) × β a) :=
  ⟨{iter := MapIterator.prependMap t .done, upper := bound }⟩

#eval (iterLE _ _ test compare 5).allowNontermination.toList

section Rxc
end Rxc
end Std.DTreeMap
