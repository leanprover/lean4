/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Init.Data.Iterators
import Init.Data.Iterators.Lemmas.Consumers.Collect
import all Init.Data.Range.Polymorphic.PRange
import all Init.Data.Range.Polymorphic.RangeIterator
import all Init.Data.Range.Polymorphic.Basic

namespace Std.PRange
open Std.Iterators

variable {shape : RangeShape} {α : Type u}

private theorem Internal.iter_open_eq_of_isSome_succ? [UpwardEnumerable α]
    [SupportsUpperBound su α] [HasFiniteRanges su α]
    [LawfulUpwardEnumerable α]
    {lo : Bound .open α} {hi} (h : (UpwardEnumerable.succ? lo).isSome) :
    Internal.iter (PRange.mk (shape := ⟨.open, su⟩) lo hi) =
      Internal.iter (PRange.mk (shape := ⟨.closed, su⟩) (UpwardEnumerable.succ? lo |>.get h) hi) := by
  simp [Internal.iter, BoundedUpwardEnumerable.init?]

private theorem Internal.toList_eq_toList_iter [UpwardEnumerable α]
    [BoundedUpwardEnumerable sl α] [SupportsUpperBound su α] [HasFiniteRanges su α]
    [LawfulUpwardEnumerable α]
    {r : PRange ⟨sl, su⟩ α} :
    r.toList = (Internal.iter r).toList := by
  rfl

theorem RangeIterator.toList_eq_match [UpwardEnumerable α]
    [SupportsUpperBound su α] [HasFiniteRanges su α]
    [LawfulUpwardEnumerable α]
    {it : Iter (α := RangeIterator su α) α} :
    it.toList =  match it.internalState.next with
      | none => []
      | some a => if SupportsUpperBound.IsSatisfied it.internalState.upperBound a then
          a :: (⟨⟨UpwardEnumerable.succ? a, it.internalState.upperBound⟩⟩ : Iter (α := RangeIterator su α) α).toList
        else
          [] := by
  rw [Iter.toList_eq_match_step, RangeIterator.step_eq_step]
  simp only [RangeIterator.step, Internal.iter]
  split <;> rename_i heq <;> simp only [Subtype.mk.injEq] at heq
  · split at heq <;> rename_i heq'
    · cases heq
    · split at heq <;> rename_i hs <;> cases heq
      simp [heq', hs]
  · split at heq <;> rename_i heq' <;> (try cases heq)
    split at heq <;> cases heq
  · split at heq <;> simp_all

private theorem toList_eq_aux [UpwardEnumerable α]
    [SupportsUpperBound su α] [HasFiniteRanges su α]
    [LawfulUpwardEnumerable α]
    {r : PRange ⟨.open, su⟩ α} :
    r.toList = match UpwardEnumerable.succ? r.lower with
      | none => []
      | some a => if SupportsUpperBound.IsSatisfied r.upper a then
        a :: (PRange.mk (shape := ⟨.open, su⟩) a r.upper).toList
      else
        [] := by
  simp only [Internal.toList_eq_toList_iter,
    show r.upper = (Internal.iter r).internalState.upperBound by rfl,
    show UpwardEnumerable.succ? r.lower = (Internal.iter r).internalState.next by rfl]
  generalize Internal.iter r = it
  rw [RangeIterator.toList_eq_match]
  split
  · simp_all
  · rename_i heq
    simp only [heq]
    split <;> rfl

theorem toList_eq [UpwardEnumerable α] [BoundedUpwardEnumerable sl α]
    [SupportsUpperBound su α] [HasFiniteRanges su α]
    [LawfulUpwardEnumerable α]
    {r : PRange ⟨sl, su⟩ α} :
    r.toList = match BoundedUpwardEnumerable.init? r.lower with
      | none => []
      | some a => if SupportsUpperBound.IsSatisfied r.upper a then
        a :: (PRange.mk (shape := ⟨.open, su⟩) a r.upper).toList
      else
        [] := by
  rw [Internal.toList_eq_toList_iter, RangeIterator.toList_eq_match,
    show (Internal.iter r).internalState.next = BoundedUpwardEnumerable.init? r.lower by rfl,
    show (Internal.iter r).internalState.upperBound = r.upper by rfl]
  split
  · rfl
  · split
    · simp only [List.cons.injEq, true_and, Internal.toList_eq_toList_iter, Internal.iter,
        BoundedUpwardEnumerable.init?]
    · rfl

private theorem toList_open_eq_of_isSome_succ? [UpwardEnumerable α]
    [SupportsUpperBound su α] [HasFiniteRanges su α]
    [LawfulUpwardEnumerable α]
    {lo : Bound .open α} {hi} (h : (UpwardEnumerable.succ? lo).isSome) :
    (PRange.mk (shape := ⟨.open, su⟩) lo hi).toList =
      (PRange.mk (shape := ⟨.closed, su⟩) (UpwardEnumerable.succ? lo |>.get h) hi).toList := by
  simp [Internal.toList_eq_toList_iter, Internal.iter_open_eq_of_isSome_succ?, h]

theorem toList_eq_nil_iff [UpwardEnumerable α]
    [SupportsUpperBound su α] [HasFiniteRanges su α] [BoundedUpwardEnumerable sl α]
    [LawfulUpwardEnumerable α]
    {r : PRange ⟨sl, su⟩ α} :
    r.toList = [] ↔
      ¬ (∃ a, BoundedUpwardEnumerable.init? r.lower = some a ∧ SupportsUpperBound.IsSatisfied r.upper a) := by
  rw [Internal.toList_eq_toList_iter] --, Iter.toList_eq_match_step, RangeIterator.step_eq_step]
  rw [RangeIterator.toList_eq_match, Internal.iter]
  simp only
  split <;> rename_i heq <;> simp [heq]

theorem RangeIterator.mem_toList_iff_isPlausibleIndirectOutput
    [UpwardEnumerable α]
    [SupportsUpperBound su α]
    [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableUpperBound su α]
    [HasFiniteRanges su α]
    {it : Iter (α := RangeIterator su α) α} :
    out ∈ it.toList ↔ it.IsPlausibleIndirectOutput out := by
  constructor
  · apply Iter.isPlausibleIndirectOutput_of_mem_toList
  · intro h
    induction h
    · rename_i it out h
      rw [RangeIterator.isPlausibleOutput_iff] at h
      rw [toList_eq_match]
      simp [h]
    · rename_i it it' out h _ h'
      rw [RangeIterator.isPlausibleSuccessorOf_iff] at h
      obtain ⟨a, ha⟩ := h
      rw [toList_eq_match]
      simp only [ha.1, ha.2.1, ha.2.2.1]
      simp [← ha.2.2.2, h']

instance [UpwardEnumerable α]
    [SupportsUpperBound su α] [HasFiniteRanges su α]
    [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableUpperBound su α] :
    LawfulPureIterator (RangeIterator su α) where
  mem_toList_iff_isPlausibleIndirectOutput :=
    RangeIterator.mem_toList_iff_isPlausibleIndirectOutput

theorem mem_toList_iff_mem [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [HasFiniteRanges su α]
    [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    {r : PRange ⟨sl, su⟩ α}
    {a : α} : a ∈ r.toList ↔ a ∈ r := by
  rw [Internal.toList_eq_toList_iter, RangeIterator.mem_toList_iff_isPlausibleIndirectOutput,
    Internal.isPlausibleIndirectOutput_iter_iff]

theorem pairwise_toList_upwardEnumerableLt [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [HasFiniteRanges su α]
    [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    {r : PRange ⟨sl, su⟩ α} :
    r.toList.Pairwise (fun a b => UpwardEnumerable.lt a b) := by
  rw [Internal.toList_eq_toList_iter]
  generalize Internal.iter r = it
  induction it using Iter.inductSteps with | step it ihy ihs =>
  rw [RangeIterator.toList_eq_match]
  repeat' split <;> (try exact .nil; done)
  rename_i a _ _
  apply List.Pairwise.cons
  · intro a' ha
    rw [RangeIterator.mem_toList_iff_isPlausibleIndirectOutput] at ha
    replace ha := RangeIterator.upwardEnumerableLe_of_isPlausibleIndirectOutput ha
    simp only at ha
    have : UpwardEnumerable.lt a ha.choose := by
      refine ⟨0, ?_⟩
      simp only [UpwardEnumerable.succMany?_succ, UpwardEnumerable.succMany?_zero,
        Option.bind_some]
      exact ha.choose_spec.1
    exact UpwardEnumerable.lt_of_lt_of_le this ha.choose_spec.2
  · apply ihy (out := a)
    simp_all [RangeIterator.isPlausibleStep_iff, RangeIterator.step]

theorem pairwise_toList_ne [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [HasFiniteRanges su α]
    [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    {r : PRange ⟨sl, su⟩ α} :
    r.toList.Pairwise (fun a b => a ≠ b) :=
  List.Pairwise.imp (fun hlt => UpwardEnumerable.ne_of_lt hlt) pairwise_toList_upwardEnumerableLt

theorem pairwise_toList_lt [LT α] [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [HasFiniteRanges su α]
    [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    {r : PRange ⟨sl, su⟩ α} :
    r.toList.Pairwise (fun a b => a < b) :=
  List.Pairwise.imp
    (fun hlt => (LawfulUpwardEnumerableLT.lt_iff ..).mpr hlt) pairwise_toList_upwardEnumerableLt

theorem pairwise_toList_le [LE α] [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [HasFiniteRanges su α]
    [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    {r : PRange ⟨sl, su⟩ α} :
    r.toList.Pairwise (fun a b => a ≤ b) :=
  pairwise_toList_upwardEnumerableLt
    |> List.Pairwise.imp UpwardEnumerable.le_of_lt
    |> List.Pairwise.imp (fun hle => (LawfulUpwardEnumerableLE.le_iff ..).mpr hle)

private theorem Internal.forIn'_eq_forIn'_iter [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [HasFiniteRanges su α]
    [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    {r : PRange ⟨sl, su⟩ α}
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    haveI := Iter.instForIn' (α := RangeIterator su α) (β := α) (n := m)
    ForIn'.forIn' r init f =
      ForIn'.forIn' (Internal.iter r) init (fun a ha acc => f a (Internal.isPlausibleIndirectOutput_iter_iff.mp ha) acc) := by
  rfl

theorem forIn'_eq_forIn'_toList [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [HasFiniteRanges su α]
    [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    {r : PRange ⟨sl, su⟩ α}
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f =
      ForIn'.forIn' r.toList init (fun a ha acc => f a (mem_toList_iff_mem.mp ha) acc) := by
  simp [Internal.forIn'_eq_forIn'_iter, Internal.toList_eq_toList_iter,
    Iter.forIn'_eq_forIn'_toList]

theorem forIn'_toList_eq_forIn' [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [HasFiniteRanges su α]
    [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    {r : PRange ⟨sl, su⟩ α}
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r.toList init f =
      ForIn'.forIn' r init (fun a ha acc => f a (mem_toList_iff_mem.mpr ha) acc) := by
  simp [forIn'_eq_forIn'_toList]

theorem mem_of_mem_open [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [HasFiniteRanges su α]
    [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    [SupportsLowerBound .open α] [LawfulUpwardEnumerableLowerBound .open α]
    {r : PRange ⟨sl, su⟩ α} {a b : α}
    (hrb : SupportsLowerBound.IsSatisfied r.lower b)
    (hmem : a ∈ PRange.mk (shape := ⟨.open, su⟩) b r.upper) :
    a ∈ r := by
  refine ⟨?_, hmem.2⟩
  have := hmem.1
  simp only [LawfulUpwardEnumerableLowerBound.isSatisfied_iff,
    BoundedUpwardEnumerable.init?] at this hrb ⊢
  obtain ⟨init, hi⟩ := hrb
  obtain ⟨b', hb'⟩ := this
  refine ⟨init, hi.1, UpwardEnumerable.le_trans hi.2 (UpwardEnumerable.le_trans ?_ hb'.2)⟩
  exact UpwardEnumerable.le_of_succ?_eq hb'.1

theorem SupportsLowerBound.isSatisfied_init? [UpwardEnumerable α]
    [SupportsLowerBound sl α] [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLowerBound sl α]
    {bound : Bound sl α} {a : α} (h : BoundedUpwardEnumerable.init? bound = some a) :
    SupportsLowerBound.IsSatisfied bound a := by
  simp only [LawfulUpwardEnumerableLowerBound.isSatisfied_iff]
  exact ⟨a, h, UpwardEnumerable.le_refl _⟩

theorem forIn'_eq_match [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [HasFiniteRanges su α]
    [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    [SupportsLowerBound .open α] [LawfulUpwardEnumerableLowerBound .open α]
    {r : PRange ⟨sl, su⟩ α}
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f = match hi : BoundedUpwardEnumerable.init? r.lower with
      | none => pure init
      | some a => if hu : SupportsUpperBound.IsSatisfied r.upper a then do
        match ← f a ⟨SupportsLowerBound.isSatisfied_init? hi, hu⟩ init with
        | .yield c =>
          ForIn'.forIn' (α := α) (β := γ) (PRange.mk (shape := ⟨.open, su⟩) a r.upper) c
            (fun a ha acc => f a (mem_of_mem_open (SupportsLowerBound.isSatisfied_init? hi) ha) acc)
        | .done c => return c
      else
        return init := by
  rw [Internal.forIn'_eq_forIn'_iter, Iter.forIn'_eq_match_step]
  simp only [RangeIterator.step_eq_step, RangeIterator.step, Internal.iter]
  apply Eq.symm
  split <;> rename_i heq
  · simp [heq]
  · simp only [heq]
    split
    · simp only
      apply bind_congr
      intro step
      split
      · simp [Internal.forIn'_eq_forIn'_iter, Internal.iter, BoundedUpwardEnumerable.init?]
      · simp
    · simp

end Std.PRange
