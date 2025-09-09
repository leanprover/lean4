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

namespace Std
open PRange

namespace Rcc

variable {α : Type u}

/--
Internal function that constructs an iterator for a `PRange`. This is an internal function.
Use `PRange.iter` instead, which requires importing `Std.Data.Iterators`.
-/
@[always_inline, inline]
def Internal.iter [UpwardEnumerable α] (r : Rcc α) : Iter (α := Rxc.Iterator α) α :=
  ⟨⟨some r.lower, r.upper⟩⟩

/--
Returns the elements of the given range as a list in ascending order, given that ranges of the given
type and shape support this function and the range is finite.
-/
@[always_inline, inline, expose]
def toList [UpwardEnumerable α] (r : Rcc α)
    [Iterator (Rxc.Iterator α) Id α] [Finite (Rxc.Iterator α) Id]
    [IteratorCollect (Rxc.Iterator α) Id Id] : List α :=
  Internal.iter r |>.toList

/--
Iterators for ranges implementing `RangeSize` support the `size` function.
-/
instance [Rxc.HasSize α] [UpwardEnumerable α] [LE α] [DecidableLE α] :
    IteratorSize (Rxc.Iterator α) Id where
  size it := match it.internalState.next with
    | none => pure (.up 0)
    | some next => pure (.up (Rxc.HasSize.size next it.internalState.upperBound))

/--
Returns the number of elements contained in the given range, given that ranges of the given
type and shape support this function.
-/
@[always_inline, inline]
def size [UpwardEnumerable α] [LE α] [DecidableLE α] (r : Rcc α)
    [IteratorSize (Rxc.Iterator α) Id] : Nat :=
  Internal.iter r |>.size

section Iterator

theorem Internal.isPlausibleIndirectOutput_iter_iff
    [UpwardEnumerable α] [LE α] [DecidableLE α] [Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·)]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    {r : Rcc α} {a : α} :
    (Internal.iter r).IsPlausibleIndirectOutput a ↔ a ∈ r := by
  rw [Rxc.Iterator.isPlausibleIndirectOutput_iff]
  constructor
  · rintro ⟨n, hn, hu⟩
    refine ⟨?_, hu⟩
    rw [LawfulUpwardEnumerableLE.le_iff]
    cases hr : (Internal.iter r).internalState.next
    · simp [hr] at hn
    · rw [hr, Option.bind_some] at hn
      cases hr
      exact ⟨n, hn⟩
  · rintro ⟨hl, hu⟩
    rw [LawfulUpwardEnumerableLE.le_iff] at hl
    obtain ⟨n, hn⟩ := hl
    exact ⟨n, by simp [Internal.iter, hn], hu⟩

open Std.Rxc.Iterator in
theorem _root_.Std.Rxc.Iterator.upwardEnumerableLe_of_isPlausibleIndirectOutput
    [UpwardEnumerable α] [LE α] [DecidableLE α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·)]
    {it : Iter (α := Rxc.Iterator α) α} {out : α}
    (hout : it.IsPlausibleIndirectOutput out) :
    ∃ a, it.internalState.next = some a ∧ UpwardEnumerable.LE a out := by
  have ⟨a, ha⟩ := Option.isSome_iff_exists.mp (isSome_next_of_isPlausibleIndirectOutput hout)
  refine ⟨a, ha, ?_⟩
  simp only [isPlausibleIndirectOutput_iff, ha, Option.bind_some, exists_and_right] at hout
  exact hout.1

@[no_expose]
instance {m} [UpwardEnumerable α]
    [LE α] [DecidableLE α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·)]
    [Monad m] [Finite (Rxc.Iterator α) Id] :
    ForIn' m (Rcc α) α inferInstance where
  forIn' r init f := by
    haveI := Iter.instForIn' (α := Rxc.Iterator α) (β := α) (n := m)
    refine ForIn'.forIn' (α := α) (Internal.iter r) init (fun a ha acc => f a ?_ acc)
    simp only [Membership.mem] at ha
    rwa [Internal.isPlausibleIndirectOutput_iter_iff] at ha

end Iterator

end Rcc

namespace Rco

variable {α : Type u}

/--
Internal function that constructs an iterator for a `PRange`. This is an internal function.
Use `PRange.iter` instead, which requires importing `Std.Data.Iterators`.
-/
@[always_inline, inline]
def Internal.iter [UpwardEnumerable α] (r : Rco α) : Iter (α := Rxo.Iterator α) α :=
  ⟨⟨some r.lower, r.upper⟩⟩

/--
Returns the elements of the given range as a list in ascending order, given that ranges of the given
type and shape support this function and the range is finite.
-/
@[always_inline, inline, expose]
def toList [UpwardEnumerable α] (r : Rco α)
    [Iterator (Rxo.Iterator α) Id α] [Finite (Rxo.Iterator α) Id]
    [IteratorCollect (Rxo.Iterator α) Id Id] : List α :=
  Internal.iter r |>.toList

/--
Iterators for ranges implementing `RangeSize` support the `size` function.
-/
instance [Rxo.HasSize α] [UpwardEnumerable α] [LT α] [DecidableLT α] :
    IteratorSize (Rxo.Iterator α) Id where
  size it := match it.internalState.next with
    | none => pure (.up 0)
    | some next => pure (.up (Rxo.HasSize.size next it.internalState.upperBound))

/--
Returns the number of elements contained in the given range, given that ranges of the given
type and shape support this function.
-/
@[always_inline, inline]
def size [UpwardEnumerable α] [LT α] [DecidableLT α] (r : Rco α)
    [IteratorSize (Rxo.Iterator α) Id] : Nat :=
  Internal.iter r |>.size

section Iterator

theorem Internal.isPlausibleIndirectOutput_iter_iff
    [UpwardEnumerable α] [LE α] [DecidableLE α] [LT α] [DecidableLT α]
    [Trans (α := α) (· < ·) (· < ·) (· < ·)] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLE α]
    {r : Rco α} {a : α} :
    (Internal.iter r).IsPlausibleIndirectOutput a ↔ a ∈ r := by
  rw [Rxo.Iterator.isPlausibleIndirectOutput_iff]
  constructor
  · rintro ⟨n, hn, hu⟩
    refine ⟨?_, hu⟩
    rw [LawfulUpwardEnumerableLE.le_iff]
    cases hr : (Internal.iter r).internalState.next
    · simp [hr] at hn
    · rw [hr, Option.bind_some] at hn
      cases hr
      exact ⟨n, hn⟩
  · rintro ⟨hl, hu⟩
    rw [LawfulUpwardEnumerableLE.le_iff] at hl
    obtain ⟨n, hn⟩ := hl
    exact ⟨n, by simp [Internal.iter, hn], hu⟩

open Std.Rxo.Iterator in
theorem _root_.Std.Rxo.Iterator.upwardEnumerableLe_of_isPlausibleIndirectOutput
    [UpwardEnumerable α] [LT α] [DecidableLT α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Trans (α := α) (· < ·) (· < ·) (· < ·)]
    {it : Iter (α := Rxo.Iterator α) α} {out : α}
    (hout : it.IsPlausibleIndirectOutput out) :
    ∃ a, it.internalState.next = some a ∧ UpwardEnumerable.LE a out := by
  have ⟨a, ha⟩ := Option.isSome_iff_exists.mp (isSome_next_of_isPlausibleIndirectOutput hout)
  refine ⟨a, ha, ?_⟩
  simp only [isPlausibleIndirectOutput_iff, ha, Option.bind_some, exists_and_right] at hout
  exact hout.1

@[no_expose]
instance {m} [UpwardEnumerable α]
    [LE α] [DecidableLE α] [LT α] [DecidableLT α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    [Trans (α := α) (· < ·) (· < ·) (· < ·)]
    [Monad m] [Finite (Rxo.Iterator α) Id] :
    ForIn' m (Rco α) α inferInstance where
  forIn' r init f := by
    haveI := Iter.instForIn' (α := Rxo.Iterator α) (β := α) (n := m)
    refine ForIn'.forIn' (α := α) (Internal.iter r) init (fun a ha acc => f a ?_ acc)
    simp only [Membership.mem] at ha
    rwa [Internal.isPlausibleIndirectOutput_iter_iff] at ha

end Iterator

end Rco

namespace Rci

variable {α : Type u}

/--
Internal function that constructs an iterator for a `PRange`. This is an internal function.
Use `PRange.iter` instead, which requires importing `Std.Data.Iterators`.
-/
@[always_inline, inline]
def Internal.iter [UpwardEnumerable α] (r : Rci α) : Iter (α := Rxi.Iterator α) α :=
  ⟨⟨some r.lower⟩⟩

/--
Returns the elements of the given range as a list in ascending order, given that ranges of the given
type and shape support this function and the range is finite.
-/
@[always_inline, inline, expose]
def toList [UpwardEnumerable α] (r : Rci α)
    [Iterator (Rxi.Iterator α) Id α] [Finite (Rxi.Iterator α) Id]
    [IteratorCollect (Rxi.Iterator α) Id Id] : List α :=
  Internal.iter r |>.toList

/--
Iterators for ranges implementing `RangeSize` support the `size` function.
-/
instance [Rxi.HasSize α] [UpwardEnumerable α] :
    IteratorSize (Rxi.Iterator α) Id where
  size it := match it.internalState.next with
    | none => pure (.up 0)
    | some next => pure (.up (Rxi.HasSize.size next))

/--
Returns the number of elements contained in the given range, given that ranges of the given
type and shape support this function.
-/
@[always_inline, inline]
def size [UpwardEnumerable α] (r : Rci α)
    [IteratorSize (Rxi.Iterator α) Id] : Nat :=
  Internal.iter r |>.size

section Iterator

theorem Internal.isPlausibleIndirectOutput_iter_iff
    [UpwardEnumerable α] [LE α] [DecidableLE α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] {r : Rci α} {a : α} :
    (Internal.iter r).IsPlausibleIndirectOutput a ↔ a ∈ r := by
  rw [Rxi.Iterator.isPlausibleIndirectOutput_iff]
  constructor
  · rintro ⟨n, hn⟩
    simp only [Membership.mem, LawfulUpwardEnumerableLE.le_iff]
    cases hr : (Internal.iter r).internalState.next
    · simp [hr] at hn
    · rw [hr, Option.bind_some] at hn
      cases hr
      exact ⟨n, hn⟩
  · intro hl
    simp only [Membership.mem, LawfulUpwardEnumerableLE.le_iff] at hl
    obtain ⟨n, hn⟩ := hl
    exact ⟨n, by simp [Internal.iter, hn]⟩

open Std.Rxi.Iterator in
theorem _root_.Std.Rxi.Iterator.upwardEnumerableLe_of_isPlausibleIndirectOutput
    [UpwardEnumerable α]
    [LawfulUpwardEnumerable α]
    {it : Iter (α := Rxi.Iterator α) α} {out : α}
    (hout : it.IsPlausibleIndirectOutput out) :
    ∃ a, it.internalState.next = some a ∧ UpwardEnumerable.LE a out := by
  have ⟨a, ha⟩ := Option.isSome_iff_exists.mp (isSome_next_of_isPlausibleIndirectOutput hout)
  refine ⟨a, ha, ?_⟩
  simpa only [isPlausibleIndirectOutput_iff, ha, Option.bind_some] using hout

@[no_expose]
instance {m} [UpwardEnumerable α]
    [LE α] [DecidableLE α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Monad m] [Finite (Rxi.Iterator α) Id] :
    ForIn' m (Rci α) α inferInstance where
  forIn' r init f := by
    haveI := Iter.instForIn' (α := Rxi.Iterator α) (β := α) (n := m)
    refine ForIn'.forIn' (α := α) (Internal.iter r) init (fun a ha acc => f a ?_ acc)
    simp only [Membership.mem] at ha
    rwa [Internal.isPlausibleIndirectOutput_iter_iff] at ha

end Iterator

end Rci

namespace Roc

variable {α : Type u}

/--
Internal function that constructs an iterator for a `PRange`. This is an internal function.
Use `PRange.iter` instead, which requires importing `Std.Data.Iterators`.
-/
@[always_inline, inline]
def Internal.iter [UpwardEnumerable α] (r : Roc α) : Iter (α := Rxc.Iterator α) α :=
  ⟨⟨UpwardEnumerable.succ? r.lower, r.upper⟩⟩

/--
Returns the elements of the given range as a list in ascending order, given that ranges of the given
type and shape support this function and the range is finite.
-/
@[always_inline, inline, expose]
def toList [UpwardEnumerable α] (r : Roc α)
    [Iterator (Rxc.Iterator α) Id α] [Finite (Rxc.Iterator α) Id]
    [IteratorCollect (Rxc.Iterator α) Id Id] : List α :=
  Internal.iter r |>.toList

/--
Iterators for ranges implementing `RangeSize` support the `size` function.
-/
instance [Rxc.HasSize α] [UpwardEnumerable α] [LE α] [DecidableLE α] :
    IteratorSize (Rxc.Iterator α) Id where
  size it := match it.internalState.next with
    | none => pure (.up 0)
    | some next => pure (.up (Rxc.HasSize.size next it.internalState.upperBound))

/--
Returns the number of elements contained in the given range, given that ranges of the given
type and shape support this function.
-/
@[always_inline, inline]
def size [UpwardEnumerable α] [LE α] [DecidableLE α] (r : Roc α)
    [IteratorSize (Rxc.Iterator α) Id] : Nat :=
  Internal.iter r |>.size

section Iterator

theorem Internal.isPlausibleIndirectOutput_iter_iff
    [UpwardEnumerable α] [LE α] [DecidableLE α] [LT α] [DecidableLT α]
    [Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·)] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLT α]
    {r : Roc α} {a : α} :
    (Internal.iter r).IsPlausibleIndirectOutput a ↔ a ∈ r := by
  rw [Rxc.Iterator.isPlausibleIndirectOutput_iff]
  constructor
  · rintro ⟨n, hn, hu⟩
    refine ⟨?_, hu⟩
    rw [LawfulUpwardEnumerableLT.lt_iff]
    cases hr : (Internal.iter r).internalState.next
    · simp [hr] at hn
    · rw [hr, Option.bind_some] at hn
      simp only [iter] at hr
      apply UpwardEnumerable.lt_of_lt_of_le
      · exact ⟨0, by simpa [UpwardEnumerable.succMany?_one]⟩
      · exact ⟨_, hn⟩
  · rintro ⟨hl, hu⟩
    rw [LawfulUpwardEnumerableLT.lt_iff] at hl
    obtain ⟨n, hn⟩ := hl
    exact ⟨n,
      by simp [Internal.iter, hn, ← UpwardEnumerable.succMany?_succ?_eq_succ?_bind_succMany?], hu⟩

@[no_expose]
instance {m} [UpwardEnumerable α]
    [LE α] [DecidableLE α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LT α] [DecidableLT α] [LawfulUpwardEnumerableLT α]
    [Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·)]
    [Monad m] [Finite (Rxc.Iterator α) Id] :
    ForIn' m (Roc α) α inferInstance where
  forIn' r init f := by
    haveI := Iter.instForIn' (α := Rxc.Iterator α) (β := α) (n := m)
    refine ForIn'.forIn' (α := α) (Internal.iter r) init (fun a ha acc => f a ?_ acc)
    simp only [Membership.mem] at ha
    rwa [Internal.isPlausibleIndirectOutput_iter_iff] at ha

end Iterator

end Roc

namespace Roo

variable {α : Type u}

/--
Internal function that constructs an iterator for a `PRange`. This is an internal function.
Use `PRange.iter` instead, which requires importing `Std.Data.Iterators`.
-/
@[always_inline, inline]
def Internal.iter [UpwardEnumerable α] (r : Roo α) : Iter (α := Rxo.Iterator α) α :=
  ⟨⟨UpwardEnumerable.succ? r.lower, r.upper⟩⟩

/--
Returns the elements of the given range as a list in ascending order, given that ranges of the given
type and shape support this function and the range is finite.
-/
@[always_inline, inline, expose]
def toList [UpwardEnumerable α] (r : Roo α)
    [Iterator (Rxo.Iterator α) Id α] [Finite (Rxo.Iterator α) Id]
    [IteratorCollect (Rxo.Iterator α) Id Id] : List α :=
  Internal.iter r |>.toList

/--
Iterators for ranges implementing `RangeSize` support the `size` function.
-/
instance [Rxo.HasSize α] [UpwardEnumerable α] [LT α] [DecidableLT α] :
    IteratorSize (Rxo.Iterator α) Id where
  size it := match it.internalState.next with
    | none => pure (.up 0)
    | some next => pure (.up (Rxo.HasSize.size next it.internalState.upperBound))

/--
Returns the number of elements contained in the given range, given that ranges of the given
type and shape support this function.
-/
@[always_inline, inline]
def size [UpwardEnumerable α] [LT α] [DecidableLT α] (r : Roo α)
    [IteratorSize (Rxo.Iterator α) Id] : Nat :=
  Internal.iter r |>.size

section Iterator

theorem Internal.isPlausibleIndirectOutput_iter_iff
    [UpwardEnumerable α] [LT α] [DecidableLT α] [LT α] [DecidableLT α]
    [Trans (α := α) (· < ·) (· < ·) (· < ·)] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLT α]
    {r : Roo α} {a : α} :
    (Internal.iter r).IsPlausibleIndirectOutput a ↔ a ∈ r := by
  rw [Rxo.Iterator.isPlausibleIndirectOutput_iff]
  constructor
  · rintro ⟨n, hn, hu⟩
    refine ⟨?_, hu⟩
    rw [LawfulUpwardEnumerableLT.lt_iff]
    cases hr : (Internal.iter r).internalState.next
    · simp [hr] at hn
    · rw [hr, Option.bind_some] at hn
      simp only [iter] at hr
      apply UpwardEnumerable.lt_of_lt_of_le
      · exact ⟨0, by simpa [UpwardEnumerable.succMany?_one]⟩
      · exact ⟨_, hn⟩
  · rintro ⟨hl, hu⟩
    rw [LawfulUpwardEnumerableLT.lt_iff] at hl
    obtain ⟨n, hn⟩ := hl
    exact ⟨n,
      by simp [Internal.iter, hn, ← UpwardEnumerable.succMany?_succ?_eq_succ?_bind_succMany?], hu⟩

@[no_expose]
instance {m} [UpwardEnumerable α]
    [LT α] [DecidableLT α] [LT α] [DecidableLT α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLT α]
    [Trans (α := α) (· < ·) (· < ·) (· < ·)]
    [Monad m] [Finite (Rxo.Iterator α) Id] :
    ForIn' m (Roo α) α inferInstance where
  forIn' r init f := by
    haveI := Iter.instForIn' (α := Rxo.Iterator α) (β := α) (n := m)
    refine ForIn'.forIn' (α := α) (Internal.iter r) init (fun a ha acc => f a ?_ acc)
    simp only [Membership.mem] at ha
    rwa [Internal.isPlausibleIndirectOutput_iter_iff] at ha

end Iterator

end Roo

namespace Roi

variable {α : Type u}

/--
Internal function that constructs an iterator for a `PRange`. This is an internal function.
Use `PRange.iter` instead, which requires importing `Std.Data.Iterators`.
-/
@[always_inline, inline]
def Internal.iter [UpwardEnumerable α] (r : Roi α) : Iter (α := Rxi.Iterator α) α :=
  ⟨⟨UpwardEnumerable.succ? r.lower⟩⟩

/--
Returns the elements of the given range as a list in ascending order, given that ranges of the given
type and shape support this function and the range is finite.
-/
@[always_inline, inline, expose]
def toList [UpwardEnumerable α] (r : Roi α)
    [Iterator (Rxi.Iterator α) Id α] [Finite (Rxi.Iterator α) Id]
    [IteratorCollect (Rxi.Iterator α) Id Id] : List α :=
  Internal.iter r |>.toList

/--
Iterators for ranges implementing `RangeSize` support the `size` function.
-/
instance [Rxi.HasSize α] [UpwardEnumerable α] :
    IteratorSize (Rxi.Iterator α) Id where
  size it := match it.internalState.next with
    | none => pure (.up 0)
    | some next => pure (.up (Rxi.HasSize.size next))

/--
Returns the number of elements contained in the given range, given that ranges of the given
type and shape support this function.
-/
@[always_inline, inline]
def size [UpwardEnumerable α] (r : Roi α)
    [IteratorSize (Rxi.Iterator α) Id] : Nat :=
  Internal.iter r |>.size

section Iterator

theorem Internal.isPlausibleIndirectOutput_iter_iff
    [UpwardEnumerable α] [LT α] [DecidableLT α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] {r : Roi α} {a : α} :
    (Internal.iter r).IsPlausibleIndirectOutput a ↔ a ∈ r := by
  rw [Rxi.Iterator.isPlausibleIndirectOutput_iff]
  constructor
  · rintro ⟨n, hn⟩
    simp only [Membership.mem, LawfulUpwardEnumerableLT.lt_iff]
    cases hr : (Internal.iter r).internalState.next
    · simp [hr] at hn
    · rw [hr, Option.bind_some] at hn
      apply UpwardEnumerable.lt_of_lt_of_le
      · exact ⟨0, by simpa [UpwardEnumerable.succMany?_one]⟩
      · exact ⟨_, hn⟩
  · intro hl
    simp only [Membership.mem, LawfulUpwardEnumerableLT.lt_iff] at hl
    obtain ⟨n, hn⟩ := hl
    exact ⟨n,
      by simp [Internal.iter, hn, ← UpwardEnumerable.succMany?_succ?_eq_succ?_bind_succMany?]⟩

@[no_expose]
instance {m} [UpwardEnumerable α]
    [LT α] [DecidableLT α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Monad m] [Finite (Rxi.Iterator α) Id] :
    ForIn' m (Roi α) α inferInstance where
  forIn' r init f := by
    haveI := Iter.instForIn' (α := Rxi.Iterator α) (β := α) (n := m)
    refine ForIn'.forIn' (α := α) (Internal.iter r) init (fun a ha acc => f a ?_ acc)
    simp only [Membership.mem] at ha
    rwa [Internal.isPlausibleIndirectOutput_iter_iff] at ha

end Iterator

end Roi

namespace Ric

variable {α : Type u}

/--
Internal function that constructs an iterator for a `PRange`. This is an internal function.
Use `PRange.iter` instead, which requires importing `Std.Data.Iterators`.
-/
@[always_inline, inline]
def Internal.iter [UpwardEnumerable α] [Least? α] (r : Ric α) : Iter (α := Rxc.Iterator α) α :=
  ⟨⟨Least?.least?, r.upper⟩⟩

/--
Returns the elements of the given range as a list in ascending order, given that ranges of the given
type and shape support this function and the range is finite.
-/
@[always_inline, inline, expose]
def toList [UpwardEnumerable α] [Least? α] (r : Ric α)
    [Iterator (Rxc.Iterator α) Id α] [Finite (Rxc.Iterator α) Id]
    [IteratorCollect (Rxc.Iterator α) Id Id] : List α :=
  Internal.iter r |>.toList

/--
Iterators for ranges implementing `RangeSize` support the `size` function.
-/
instance [Rxc.HasSize α] [UpwardEnumerable α] [LE α] [DecidableLE α] :
    IteratorSize (Rxc.Iterator α) Id where
  size it := match it.internalState.next with
    | none => pure (.up 0)
    | some next => pure (.up (Rxc.HasSize.size next it.internalState.upperBound))

/--
Returns the number of elements contained in the given range, given that ranges of the given
type and shape support this function.
-/
@[always_inline, inline]
def size [UpwardEnumerable α] [Least? α] [LE α] [DecidableLE α] (r : Ric α)
    [IteratorSize (Rxc.Iterator α) Id] : Nat :=
  Internal.iter r |>.size

section Iterator

theorem Internal.isPlausibleIndirectOutput_iter_iff
    [UpwardEnumerable α] [Least? α] [LE α] [DecidableLE α] [Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·)]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    {r : Ric α} {a : α} :
    (Internal.iter r).IsPlausibleIndirectOutput a ↔ a ∈ r := by
  rw [Rxc.Iterator.isPlausibleIndirectOutput_iff]
  constructor
  · rintro ⟨n, hn, hu⟩
    simp only [Membership.mem, LawfulUpwardEnumerableLE.le_iff]
    cases hr : (Internal.iter r).internalState.next
    · simp [hr] at hn
    · simpa [LawfulUpwardEnumerableLE.le_iff] using hu
  · intro hu
    simp only [Membership.mem, LawfulUpwardEnumerableLE.le_iff] at hu
    simp [iter]
    obtain ⟨n, hn⟩ := hu
    exact ⟨n, by simp [Internal.iter, hn], hu⟩

open Std.Rxc.Iterator in
theorem _root_.Std.Rxc.Iterator.upwardEnumerableLe_of_isPlausibleIndirectOutput
    [UpwardEnumerable α] [LE α] [DecidableLE α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·)]
    {it : Iter (α := Rxc.Iterator α) α} {out : α}
    (hout : it.IsPlausibleIndirectOutput out) :
    ∃ a, it.internalState.next = some a ∧ UpwardEnumerable.LE a out := by
  have ⟨a, ha⟩ := Option.isSome_iff_exists.mp (isSome_next_of_isPlausibleIndirectOutput hout)
  refine ⟨a, ha, ?_⟩
  simp only [isPlausibleIndirectOutput_iff, ha, Option.bind_some, exists_and_right] at hout
  exact hout.1

@[no_expose]
instance {m} [UpwardEnumerable α]
    [LE α] [DecidableLE α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·)]
    [Monad m] [Finite (Rxc.Iterator α) Id] :
    ForIn' m (Ric α) α inferInstance where
  forIn' r init f := by
    haveI := Iter.instForIn' (α := Rxc.Iterator α) (β := α) (n := m)
    refine ForIn'.forIn' (α := α) (Internal.iter r) init (fun a ha acc => f a ?_ acc)
    simp only [Membership.mem] at ha
    rwa [Internal.isPlausibleIndirectOutput_iter_iff] at ha

end Iterator

end Ric

end Std
