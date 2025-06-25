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
Returns the number of elements contained in the given range, given that ranges of the given
type and shape support this function.
-/
@[always_inline, inline]
def size [UpwardEnumerable α] [BoundedUpwardEnumerable sl α]
    [SupportsUpperBound su α] (r : PRange ⟨sl, su⟩ α)
    [IteratorSize (RangeIterator su α) Id] : Nat :=
  PRange.Internal.iter r |>.size

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

theorem PRange.mem.upper [LE α] [DecidableLE α] {i : α} {r : PRange ⟨.unbounded, .closed⟩ α} (h : i ∈ r) : i ≤ r.upper :=
  h.2

-- theorem Range.mem.lower [LE α] {i : α} {r : PRange ⟨.unbounded, .closed⟩ α} (h : i ∈ r) : r.lower ≤ i := h.1

-- theorem Range.mem.step {i : Nat} {r : PRange shape α} (h : i ∈ r) : (i - r.start) % r.step = 0 := h.2.2

theorem PRange.get_elem_helper {i n : Nat} {r : PRange ⟨.closed, .open⟩ Nat} (h₁ : i ∈ r) (h₂ : r.upper = n) :
    i < n := h₂ ▸ h₁.2

macro_rules
  | `(tactic| get_elem_tactic_extensible) => `(tactic| apply Range.get_elem_helper; assumption; rfl)

end Std.PRange
