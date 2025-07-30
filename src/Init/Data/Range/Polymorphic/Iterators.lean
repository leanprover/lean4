/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Range.Polymorphic.RangeIterator
public import Init.Data.Range.Polymorphic.Basic
public import Init.Data.Iterators.Combinators.Attach

@[expose] public section

open Std.Iterators

namespace Std.PRange

/--
Internal function that constructs an iterator for a `PRange`. This is an internal function.
Use `PRange.iter` instead, which requires importing `Std.Data.Iterators`.
-/
@[always_inline, inline]
def Internal.iter {sl su α} [UpwardEnumerable α] [BoundedUpwardEnumerable sl α]
    (r : PRange ⟨sl, su⟩ α) : Iter (α := RangeIterator su α) α :=
  ⟨⟨BoundedUpwardEnumerable.init? r.lower, r.upper⟩⟩

/--
Returns the elements of the given range as a list in ascending order, given that ranges of the given
type and shape support this function and the range is finite.
-/
@[always_inline, inline, expose]
def toList {sl su α} [UpwardEnumerable α] [BoundedUpwardEnumerable sl α]
    [SupportsUpperBound su α]
    (r : PRange ⟨sl, su⟩ α)
    [Iterator (RangeIterator su α) Id α] [Finite (RangeIterator su α) Id]
    [IteratorCollect (RangeIterator su α) Id Id] : List α :=
  PRange.Internal.iter r |>.toList

/--
Iterators for ranges implementing `RangeSize` support the `size` function.
-/
instance [RangeSize su α] [UpwardEnumerable α] [SupportsUpperBound su α] :
    IteratorSize (RangeIterator su α) Id where
  size it := match it.internalState.next with
    | none => pure (.up 0)
    | some next => pure (.up (RangeSize.size it.internalState.upperBound next))

/--
Returns the number of elements contained in the given range, given that ranges of the given
type and shape support this function.
-/
@[always_inline, inline]
def size {sl su α} [UpwardEnumerable α] [BoundedUpwardEnumerable sl α]
    [SupportsUpperBound su α] (r : PRange ⟨sl, su⟩ α)
    [IteratorSize (RangeIterator su α) Id] : Nat :=
  PRange.Internal.iter r |>.size

section Iterator

theorem Internal.isPlausibleIndirectOutput_iter_iff {sl su α}
    [UpwardEnumerable α] [BoundedUpwardEnumerable sl α]
    [SupportsLowerBound sl α] [SupportsUpperBound su α]
    [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableUpperBound su α] [LawfulUpwardEnumerableLowerBound sl α]
    {r : PRange ⟨sl, su⟩ α} {a : α} :
    (PRange.Internal.iter r).IsPlausibleIndirectOutput a ↔ a ∈ r := by
  rw [RangeIterator.isPlausibleIndirectOutput_iff]
  constructor
  · rintro ⟨n, hn, hu⟩
    refine ⟨?_, hu⟩
    rw [LawfulUpwardEnumerableLowerBound.isSatisfied_iff]
    cases hr : (PRange.Internal.iter r).internalState.next
    · simp [hr] at hn
    · rw [hr, Option.bind_some] at hn
      exact ⟨_, hr, n, hn⟩
  · rintro ⟨hl, hu⟩
    rw [LawfulUpwardEnumerableLowerBound.isSatisfied_iff] at hl
    obtain ⟨_, hr, n, hn⟩ := hl
    exact ⟨n, by simp [PRange.Internal.iter, hr, hn], hu⟩

theorem RangeIterator.upwardEnumerableLe_of_isPlausibleIndirectOutput {su α}
    [UpwardEnumerable α] [SupportsUpperBound su α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableUpperBound su α]
    {it : Iter (α := RangeIterator su α) α} {out : α}
    (hout : it.IsPlausibleIndirectOutput out) :
    ∃ a, it.internalState.next = some a ∧ UpwardEnumerable.LE a out := by
  have ⟨a, ha⟩ := Option.isSome_iff_exists.mp <|
    RangeIterator.isSome_next_of_isPlausibleIndirectOutput hout
  refine ⟨a, ha, ?_⟩
  simp only [isPlausibleIndirectOutput_iff, ha, Option.bind_some, exists_and_right] at hout
  exact hout.1

@[no_expose]
instance {sl su α m} [UpwardEnumerable α] [BoundedUpwardEnumerable sl α]
    [SupportsLowerBound sl α] [SupportsUpperBound su α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    [Monad m] [Finite (RangeIterator su α) Id] :
    ForIn' m (PRange ⟨sl, su⟩ α) α inferInstance where
  forIn' r init f := by
    haveI := Iter.instForIn' (α := RangeIterator su α) (β := α) (n := m)
    refine ForIn'.forIn' (α := α) (PRange.Internal.iter r) init (fun a ha acc => f a ?_ acc)
    simp only [Membership.mem] at ha
    rwa [PRange.Internal.isPlausibleIndirectOutput_iter_iff] at ha

end Iterator

end Std.PRange
