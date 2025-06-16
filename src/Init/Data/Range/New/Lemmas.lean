module

prelude
import all Init.Data.Range.New.Basic
import all Init.Data.Range.New.RangeIterator
import all Init.Data.Range.New.Iteration
import Init.Data.Iterators.Lemmas.Consumers.Collect

namespace Std.PRange
open Std.Iterators

variable {shape : RangeShape} {α : Type u}

private theorem toList_eq_toList_iterInternal [HasRange shape α] [UpwardEnumerable α]
    [UpwardEnumerableRange shape α] [FinitelyEnumerableRange shape α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableRange shape α]
    {r : PRange shape α} :
    r.toList = r.iterInternal.toList := by
  rfl

-- observations:
-- would be nice to have non-dependent eq_match_step lemmas
-- need to support left-closed ranges as soon as any kind of range is supported
theorem toList_eq_match [HasRange shape α] [UpwardEnumerable α]
    [UpwardEnumerableRange shape α] [FinitelyEnumerableRange shape α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableRange shape α]
    {r : PRange shape α} :
    r.toList = match UpwardEnumerableRange.init r.lower with
      | none => []
      | some a => a ::  := by sorry

theorem toList_eq_nil_iff [HasRange shape α] [UpwardEnumerable α]
    [UpwardEnumerableRange shape α] [FinitelyEnumerableRange shape α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableRange shape α]
    {r : PRange shape α} :
    r.toList = [] ↔
      ¬ (∃ a, UpwardEnumerableRange.init r.lower = some a ∧ HasRange.SatisfiesUpperBound r.upper a) := by
  rw [toList_eq_toList_iterInternal, Iter.toList_eq_match_step, Types.RangeIterator.step_eq_step]
  simp only [Types.RangeIterator.step, PRange.iterInternal]
  split <;> rename_i heq <;> simp only [Subtype.mk.injEq] at heq
  · split at heq
    · cases heq
    · split at heq
      · simp_all
      · cases heq
  · split at heq
    · cases heq
    · split at heq <;> cases heq
  · split at heq
    · simp_all
    · rename_i heq'
      split at heq
      · cases heq
      · simp_all

theorem mem_of_mem_toList [HasRange shape α] [UpwardEnumerable α]
    [UpwardEnumerableRange shape α] [FinitelyEnumerableRange shape α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableRange shape α]
    {r : PRange shape α}
    {a : α} (h : a ∈ r.toList) :
    a ∈ r := by
  rw [toList_eq_toList_iterInternal] at h
  replace h := Iter.isPlausibleIndirectOutput_of_mem_toList h

end Std.PRange
