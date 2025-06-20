/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Init.Data.Range.Polymorphic.RangeIterator

open Std.Iterators

namespace Std.PRange

/--
Internal function that constructs an iterator for a `PRange`. This is an internal function.
Use `PRange.iter` instead, which requires importing `Std.Data.Iterators`.
-/
@[always_inline, inline]
def Internal.iter [UpwardEnumerable α] [BoundedUpwardEnumerable sl α]
    (r : PRange ⟨sl, su⟩ α) : Iter (α := RangeIterator su α) α :=
  ⟨⟨BoundedUpwardEnumerable.init? r.lower, r.upper⟩⟩

/--
Returns the elements of the given range as a list in ascending order, given that ranges of the given
type and shape support this function and the range is finite.
-/
@[always_inline, inline]
def toList [UpwardEnumerable α] [BoundedUpwardEnumerable sl α]
    [SupportsUpperBound su α]
    (r : PRange ⟨sl, su⟩ α)
    [Iterator (RangeIterator su α) Id α] [Finite (RangeIterator su α) Id]
    [IteratorCollect (RangeIterator su α) Id Id] : List α :=
  PRange.Internal.iter r |>.toList

/--
This typeclass provides support for the `PRange.size` function.

The returned size should be equal to the number of elements returned by `toList`. This condition
is captured by the typeclass `LawfulRangeSize`.
-/
class RangeSize (shape : BoundShape) (α : Type u) where
  /-- Returns the number of elements starting from `init` that satisfy the given upper bound. -/
  size : (upperBound : Bound shape α) → (init : α) → Nat

class LawfulRangeSize (su : BoundShape) (α : Type u) [UpwardEnumerable α]
    [SupportsUpperBound su α] [RangeSize su α]
    [LawfulUpwardEnumerable α] [HasFiniteRanges su α] where
  size_eq_zero_of_not_satisfied (upperBound : Bound su α) (init : α)
      (h : ¬ SupportsUpperBound.IsSatisfied upperBound init) :
      RangeSize.size upperBound init = 0
  size_eq_one_of_succ?_eq_none (upperBound : Bound su α) (init : α)
      (h : SupportsUpperBound.IsSatisfied upperBound init)
      (h' : UpwardEnumerable.succ? init = none) :
      RangeSize.size upperBound init = 1
  size_eq_succ_of_succ?_eq_some (upperBound : Bound su α) (init : α)
      (h : SupportsUpperBound.IsSatisfied upperBound init)
      (h' : UpwardEnumerable.succ? init = some a) :
      RangeSize.size upperBound init = RangeSize.size upperBound a + 1

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
def size [UpwardEnumerable α] [BoundedUpwardEnumerable sl α]
    [SupportsUpperBound su α] (r : PRange ⟨sl, su⟩ α)
    [IteratorSize (RangeIterator su α) Id] : Nat :=
  PRange.Internal.iter r |>.size

section Iterator

theorem RangeIterator.isPlausibleIndirectOutput_iff
    [UpwardEnumerable α] [SupportsUpperBound su α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableUpperBound su α]
    {it : Iter (α := RangeIterator su α) α} {out : α} :
    it.IsPlausibleIndirectOutput out ↔
      ∃ n, it.internalState.next.bind (UpwardEnumerable.succMany? n ·) = some out ∧
        SupportsUpperBound.IsSatisfied it.internalState.upperBound out := by
  constructor
  · intro h
    induction h
    case direct h =>
      rw [RangeIterator.isPlausibleOutput_iff] at h
      refine ⟨0, by simp [h, LawfulUpwardEnumerable.succMany?_zero]⟩
    case indirect h _ ih =>
      rw [RangeIterator.isPlausibleSuccessorOf_iff] at h
      obtain ⟨n, hn⟩ := ih
      obtain ⟨a, ha, h₁, h₂, h₃⟩ := h
      refine ⟨n + 1, ?_⟩
      simp [ha, ← h₃, hn.2, LawfulUpwardEnumerable.succMany?_succ_eq_succ_bind_succMany, h₂, hn]
  · rintro ⟨n, hn, hu⟩
    induction n generalizing it
    case zero =>
      apply Iter.IsPlausibleIndirectOutput.direct
      rw [RangeIterator.isPlausibleOutput_iff]
      exact ⟨by simpa [LawfulUpwardEnumerable.succMany?_zero] using hn, hu⟩
    case succ ih =>
      cases hn' : it.internalState.next
      · simp [hn'] at hn
      rename_i a
      simp only [hn', Option.bind_some] at hn
      have hle : UpwardEnumerable.le a out := ⟨_, hn⟩
      rw [LawfulUpwardEnumerable.succMany?_succ_eq_succ_bind_succMany] at hn
      cases hn' : UpwardEnumerable.succ? a
      · simp only [hn', Option.bind_none, reduceCtorEq] at hn
      rename_i a'
      simp only [hn', Option.bind_some] at hn
      specialize ih (it := ⟨some a', it.internalState.upperBound⟩) hn hu
      refine Iter.IsPlausibleIndirectOutput.indirect ?_ ih
      rw [RangeIterator.isPlausibleSuccessorOf_iff]
      refine ⟨a, ‹_›, ?_, hn', rfl⟩
      apply LawfulUpwardEnumerableUpperBound.isSatisfied_of_le _ a out
      · exact hu
      · exact hle

theorem Internal.isPlausibleIndirectOutput_iter_iff
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
    rw [hr, Option.bind_some] at hn
    exact ⟨_, hr, n, hn⟩
  · rintro ⟨hl, hu⟩
    rw [LawfulUpwardEnumerableLowerBound.isSatisfied_iff] at hl
    obtain ⟨_, hr, n, hn⟩ := hl
    exact ⟨n, by simp [PRange.Internal.iter, hr, hn], hu⟩

theorem RangeIterator.upwardEnumerableLe_of_isPlausibleIndirectOutput
    [UpwardEnumerable α] [SupportsUpperBound su α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableUpperBound su α]
    {it : Iter (α := RangeIterator su α) α} {out : α}
    (hout : it.IsPlausibleIndirectOutput out) :
    ∃ a, it.internalState.next = some a ∧ UpwardEnumerable.le a out := by
  have ⟨a, ha⟩ := Option.isSome_iff_exists.mp <|
    RangeIterator.isSome_next_of_isPlausibleIndirectOutput hout
  refine ⟨a, ha, ?_⟩
  simp only [isPlausibleIndirectOutput_iff, ha, Option.bind_some, exists_and_right] at hout
  exact hout.1

@[no_expose]
instance [UpwardEnumerable α] [BoundedUpwardEnumerable sl α]
    [SupportsLowerBound sl α] [SupportsUpperBound su α]
    [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    [Monad m] [Finite (RangeIterator su α) Id] :
    ForIn' m (PRange ⟨sl, su⟩ α) α inferInstance where
  forIn' r init f := by
    haveI : MonadLift Id m := ⟨Std.Internal.idToMonad (α := _)⟩
    haveI := Iter.instForIn' (α := RangeIterator su α) (β := α) (n := m)
    refine ForIn'.forIn' (α := α) (PRange.Internal.iter r) init (fun a ha acc => f a ?_ acc)
    simp only [Membership.mem] at ha
    rwa [PRange.Internal.isPlausibleIndirectOutput_iter_iff] at ha

end Iterator

theorem le_upper_of_mem [LE α] [DecidableLE α] [SupportsLowerBound sl α]
    {a : α} {r : PRange ⟨sl, .closed⟩ α} (h : a ∈ r) : a ≤ r.upper :=
  h.2

theorem lt_upper_of_mem [LT α] [DecidableLT α] [SupportsLowerBound sl α]
    {a : α} {r : PRange ⟨sl, .open⟩ α} (h : a ∈ r) : a < r.upper :=
  h.2

theorem lower_le_of_mem [LE α] [DecidableLE α] [SupportsUpperBound su α]
    {a : α} {r : PRange ⟨.closed, su⟩ α} (h : a ∈ r) : r.lower ≤ a :=
  h.1

theorem lower_lt_of_mem [LT α] [DecidableLT α] [SupportsUpperBound su α]
    {a : α} {r : PRange ⟨.open, su⟩ α} (h : a ∈ r) : r.lower < a :=
  h.1

theorem Internal.get_elem_helper_upper_open [SupportsLowerBound sl α] [LT α] [DecidableLT α]
    {a n : α} {r : PRange ⟨sl, .open⟩ α} (h₁ : a ∈ r) (h₂ : r.upper = n) :
    a < n := h₂ ▸ r.lt_upper_of_mem h₁

macro_rules
  | `(tactic| get_elem_tactic_extensible) =>
    `(tactic| apply Range.get_elem_helper_upper_open; assumption; rfl)

end Std.PRange
