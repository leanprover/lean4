module

prelude
import Init.Data.Iterators
import all Init.Data.Range.New.Basic
import all Init.Data.Range.New.RangeIterator
import all Init.Data.Range.New.Iteration
import Init.Data.Iterators.Lemmas.Consumers.Collect

namespace Std.PRange
open Std.Iterators

variable {shape : RangeShape} {α : Type u}

private theorem toList_eq_toList_iterInternal [UpwardEnumerable α]
    [UpwardEnumerableRange sl α] [SupportsUpperBound su α] [FinitelyEnumerableRange su α]
    [LawfulUpwardEnumerable α]
    {r : PRange ⟨sl, su⟩ α} :
    r.toList = r.iterInternal.toList := by
  rfl

theorem toList_eq_match [UpwardEnumerable α]
    [SupportsUpperBound su α] [FinitelyEnumerableRange su α]
    [LawfulUpwardEnumerable α]
    {it : Iter (α := Types.RangeIterator ⟨sl, su⟩ α) α} :
    it.toList =  match it.internalState.next with
      | none => []
      | some a => if SupportsUpperBound.IsSatisfied it.internalState.upperBound a then
          a :: (⟨⟨UpwardEnumerable.succ? a, it.internalState.upperBound⟩⟩ : Iter (α := Types.RangeIterator ⟨sl, su⟩ α) α).toList
        else
          [] := by
  rw [Iter.toList_eq_match_step, Types.RangeIterator.step_eq_step]
  simp only [Types.RangeIterator.step, PRange.iterInternal]
  split <;> rename_i heq <;> simp only [Subtype.mk.injEq] at heq
  · split at heq <;> rename_i heq'
    · cases heq
    · split at heq <;> rename_i hs <;> cases heq
      simp [heq', hs]
  · split at heq <;> rename_i heq' <;> (try cases heq)
    split at heq <;> cases heq
  · split at heq <;> simp_all

theorem toList_eq_nil_iff [UpwardEnumerable α]
    [SupportsUpperBound su α] [FinitelyEnumerableRange su α] [UpwardEnumerableRange sl α]
    [LawfulUpwardEnumerable α]
    {r : PRange ⟨sl, su⟩ α} :
    r.toList = [] ↔
      ¬ (∃ a, UpwardEnumerableRange.init r.lower = some a ∧ SupportsUpperBound.IsSatisfied r.upper a) := by
  rw [toList_eq_toList_iterInternal] --, Iter.toList_eq_match_step, Types.RangeIterator.step_eq_step]
  rw [toList_eq_match, PRange.iterInternal]
  simp only
  split <;> rename_i heq <;> simp [heq]

theorem RangeIterator.mem_toList_iff_isPlausibleIndirectOutput
    [UpwardEnumerable α] [UpwardEnumerableRange sl α]
    [SupportsLowerBound sl α] [SupportsUpperBound su α]
    [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableUpperBound su α] [LawfulUpwardEnumerableLowerBound sl α]
    [FinitelyEnumerableRange su α]
    {it : Iter (α := Types.RangeIterator ⟨sl, su⟩ α) α} :
    out ∈ it.toList ↔ it.IsPlausibleIndirectOutput out := by
  constructor
  · apply Iter.isPlausibleIndirectOutput_of_mem_toList
  · intro h
    induction h
    · rename_i it out h
      rw [Types.RangeIterator.isPlausibleOutput_iff] at h
      rw [toList_eq_match]
      simp [h]
    · rename_i it it' out h _ h'
      rw [Types.RangeIterator.isPlausibleSuccessorOf_iff] at h
      obtain ⟨a, ha⟩ := h
      rw [toList_eq_match]
      simp only [ha.1, ha.2.1, ha.2.2.1]
      simp [← ha.2.2.2, h']

instance [UpwardEnumerable α]
    [SupportsLowerBound sl α] [SupportsUpperBound su α] [FinitelyEnumerableRange su α]
    [LawfulUpwardEnumerable α] [UpwardEnumerableRange sl α]
    [LawfulUpwardEnumerableUpperBound su α] [LawfulUpwardEnumerableLowerBound sl α] :
    LawfulPureIterator (Types.RangeIterator ⟨sl, su⟩ α) where
  mem_toList_iff_isPlausibleIndirectOutput :=
    RangeIterator.mem_toList_iff_isPlausibleIndirectOutput

theorem mem_toList_iff_mem [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [FinitelyEnumerableRange su α]
    [UpwardEnumerableRange sl α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    {r : PRange ⟨sl, su⟩ α}
    {a : α} : a ∈ r.toList ↔ a ∈ r := by
  rw [toList_eq_toList_iterInternal, RangeIterator.mem_toList_iff_isPlausibleIndirectOutput,
    RangeIterator.isPlausibleIndirectOutput_iff]

theorem pairwise_upwardEnumerableLt [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [FinitelyEnumerableRange su α]
    [UpwardEnumerableRange sl α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    {r : PRange ⟨sl, su⟩ α} :
    r.toList.Pairwise (fun a b => UpwardEnumerable.lt a b) := by
  rw [PRange.toList_eq_toList_iterInternal]
  generalize r.iterInternal = it
  induction it using Iter.inductSteps with | step it ihy ihs =>
  rw [toList_eq_match]
  repeat' split <;> (try exact .nil; done)
  rename_i a _ _
  apply List.Pairwise.cons
  · intro a' ha
    rw [RangeIterator.mem_toList_iff_isPlausibleIndirectOutput] at ha
    replace ha := RangeIterator.upwardEnumerableLe_of_isPlausibleIndirectOutput ha
    simp only at ha
    have : UpwardEnumerable.lt a ha.choose := by
      refine ⟨0, ?_⟩
      simp only [LawfulUpwardEnumerable.succMany?_succ, LawfulUpwardEnumerable.succMany?_zero,
        Option.bind_some]
      exact ha.choose_spec.1
    exact UpwardEnumerable.lt_of_lt_of_le this ha.choose_spec.2
  · apply ihy (out := a)
    simp_all [Types.RangeIterator.isPlausibleStep_iff, Types.RangeIterator.step]

theorem forIn'_eq_forIn'_iterInternal [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [FinitelyEnumerableRange su α]
    [UpwardEnumerableRange sl α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    {r : PRange ⟨sl, su⟩ α}
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f =
      ForIn'.forIn' r.iterInternal init (fun a ha acc => f a (RangeIterator.isPlausibleIndirectOutput_iff.mp ha) acc) := by
  rfl

theorem forIn'_eq_forIn'_toList [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [FinitelyEnumerableRange su α]
    [UpwardEnumerableRange sl α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    {r : PRange ⟨sl, su⟩ α}
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f =
      ForIn'.forIn' r.toList init (fun a ha acc => f a (mem_toList_iff_mem.mp ha) acc) := by
  simp [forIn'_eq_forIn'_iterInternal, toList_eq_toList_iterInternal,
    Iter.forIn'_eq_forIn'_toList]

theorem forIn'_toList_eq_forIn' [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [FinitelyEnumerableRange su α]
    [UpwardEnumerableRange sl α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    {r : PRange ⟨sl, su⟩ α}
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r.toList init f =
      ForIn'.forIn' r init (fun a ha acc => f a (mem_toList_iff_mem.mpr ha) acc) := by
  simp [forIn'_eq_forIn'_toList]

end Std.PRange
