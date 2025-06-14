module

prelude
import all Init.Data.Range.New.Basic
import all Init.Data.Range.New.RangeIterator
import Init.Data.Iterators.Lemmas.Consumers.Collect

namespace Std.PRange
open Std.Iterators

variable {α : Type u}

#check Std.Iterators.Iter.isPlausibleIndirectOutput_of_mem_toList

theorem toList_eq_toList_iterInternal [Succ? α] [LE α] [DecidableLE α]
    {r : PRange ⟨.closed, .closed⟩ α} :
    r.toList = r.iterInternal.toList := by
  rfl

theorem toList_eq_nil_iff [Succ? α] [LE α] [DecidableLE α] {r : PRange ⟨.closed, .closed⟩ α} :
    r.toList = [] ↔ ¬ (r.lower ≤ r.upper) := by
  rw [toList_eq_toList_iterInternal, Iter.toList_eq_match_step, Types.RangeIterator.step_eq_step]
  simp only [Types.RangeIterator.step]


theorem mem_of_mem_toList [Succ? α] [LE α] [DecidableLE α] {r : PRange ⟨.closed, .closed⟩ α}
    {a : α} (h : a ∈ r.toList) :
    a ∈ r := by
  rw [toList_eq_toList_iterInternal] at h
  replace h := Iter.isPlausibleIndirectOutput_of_mem_toList h

end Std.PRange
