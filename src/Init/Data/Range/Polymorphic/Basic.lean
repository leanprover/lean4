/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Range.Polymorphic.PRange

public section

namespace Std
open PRange

namespace Rxc

variable {α : Type u} {lo hi : α} {a : α}

/--
This typeclass provides support for the `PRange.size` function.

The returned size should be equal to the number of elements returned by `toList`. This condition
is captured by the typeclass `LawfulRangeSize`.
-/
class HasSize (α : Type u) where
  /-- Returns the number of elements starting from `lo` that satisfy the given upper bound. -/
  size (lo hi : α) : Nat

/--
This typeclass ensures that a `RangeSize` instance returns the correct size for all ranges.
-/
class LawfulHasSize (α : Type u) [LE α] [UpwardEnumerable α] [HasSize α] where
  /-- If the smallest value in the range is beyond the upper bound, the size is zero. -/
  size_eq_zero_of_not_le (lo hi : α) (h : ¬ lo ≤ hi) : HasSize.size lo hi = 0
  /--
  If the smallest value in the range satisfies the upper bound and has no successor, the size is
  one.
  -/
  size_eq_one_of_succ?_eq_none (lo hi : α)
      (h : lo ≤ hi) (h' : UpwardEnumerable.succ? lo = none) :
      HasSize.size lo hi = 1
  /--
  If the smallest value in the range satisfies the upper bound and has a successor, the size is
  one larger than the size of the range starting at the successor. -/
  size_eq_succ_of_succ?_eq_some (lo hi lo' : α)
      (h : lo ≤ hi)
      (h' : UpwardEnumerable.succ? lo = some lo') :
      HasSize.size lo hi = HasSize.size lo' hi + 1

export LawfulHasSize (size_eq_zero_of_not_le size_eq_one_of_succ?_eq_none
  size_eq_succ_of_succ?_eq_some)

theorem size_eq_zero_iff_not_le {α : Type u}
    [LE α] [UpwardEnumerable α] [HasSize α] [LawfulHasSize α]
    {lo hi : α} :
    HasSize.size lo hi = 0 ↔ ¬ lo ≤ hi := by
  open Classical in
  match h : decide (lo ≤ hi) with
  | true =>
    simp only [decide_eq_true_eq] at h
    match hs : UpwardEnumerable.succ? lo with
    | none => simp [h, LawfulHasSize.size_eq_one_of_succ?_eq_none (h := h) (h' := hs)]
    | some b => simp [h, LawfulHasSize.size_eq_succ_of_succ?_eq_some (h := h) (h' := hs)]
  | false =>
    simp only [decide_eq_false_iff_not] at h
    simp [h, LawfulHasSize.size_eq_zero_of_not_le]

theorem size_pos_iff_isSatisfied {α : Type u}
    [LE α] [UpwardEnumerable α] [HasSize α] [LawfulHasSize α]
    {lo hi : α} :
    0 < HasSize.size lo hi ↔ lo ≤ hi := by
  have := size_eq_zero_iff_not_le (lo := lo) (hi := hi)
  open Classical in
  match h : decide (lo ≤ hi) with
  | true =>
    simp only [decide_eq_true_eq] at h
    simp_all [Nat.pos_iff_ne_zero]
  | false =>
    simp only [decide_eq_false_iff_not] at h
    simp_all

end Rxc

namespace Rxo

variable {α : Type u} {lo hi : α} {a : α}

/--
This typeclass provides support for the `PRange.size` function.

The returned size should be equal to the number of elements returned by `toList`. This condition
is captured by the typeclass `LawfulRangeSize`.
-/
class HasSize (α : Type u) where
  /-- Returns the number of elements starting from `lo` that satisfy the given upper bound. -/
  size (lo hi : α) : Nat

/--
This typeclass ensures that a `RangeSize` instance returns the correct size for all ranges.
-/
class LawfulHasSize (α : Type u) [LT α] [UpwardEnumerable α] [HasSize α] where
  /-- If the smallest value in the range is beyond the upper bound, the size is zero. -/
  size_eq_zero_of_not_le (lo hi : α) (h : ¬ lo < hi) : HasSize.size lo hi = 0
  /--
  If the smallest value in the range satisfies the upper bound and has no successor, the size is
  one.
  -/
  size_eq_one_of_succ?_eq_none (lo hi : α)
      (h : lo < hi) (h' : UpwardEnumerable.succ? lo = none) :
      HasSize.size lo hi = 1
  /--
  If the smallest value in the range satisfies the upper bound and has a successor, the size is
  one larger than the size of the range starting at the successor. -/
  size_eq_succ_of_succ?_eq_some (lo hi lo' : α)
      (h : lo < hi)
      (h' : UpwardEnumerable.succ? lo = some lo') :
      HasSize.size lo hi = HasSize.size lo' hi + 1

export LawfulHasSize (size_eq_zero_of_not_le size_eq_one_of_succ?_eq_none
  size_eq_succ_of_succ?_eq_some)

theorem size_eq_zero_iff_not_le {α : Type u}
    [LT α] [UpwardEnumerable α] [HasSize α] [LawfulHasSize α]
    {lo hi : α} :
    HasSize.size lo hi = 0 ↔ ¬ lo < hi := by
  open Classical in
  match h : decide (lo < hi) with
  | true =>
    simp only [decide_eq_true_eq] at h
    match hs : UpwardEnumerable.succ? lo with
    | none => simp [h, LawfulHasSize.size_eq_one_of_succ?_eq_none (h := h) (h' := hs)]
    | some b => simp [h, LawfulHasSize.size_eq_succ_of_succ?_eq_some (h := h) (h' := hs)]
  | false =>
    simp only [decide_eq_false_iff_not] at h
    simp [h, LawfulHasSize.size_eq_zero_of_not_le]

theorem size_pos_iff_isSatisfied {α : Type u}
    [LT α] [UpwardEnumerable α] [HasSize α] [LawfulHasSize α]
    {lo hi : α} :
    0 < HasSize.size lo hi ↔ lo < hi := by
  have := size_eq_zero_iff_not_le (lo := lo) (hi := hi)
  open Classical in
  match h : decide (lo < hi) with
  | true =>
    simp only [decide_eq_true_eq] at h
    simp_all [Nat.pos_iff_ne_zero]
  | false =>
    simp only [decide_eq_false_iff_not] at h
    simp_all

end Rxo

namespace Rxi

variable {α : Type u} {lo : α} {a : α}

/--
This typeclass provides support for the `PRange.size` function.

The returned size should be equal to the number of elements returned by `toList`. This condition
is captured by the typeclass `LawfulRangeSize`.
-/
class HasSize (α : Type u) where
  /-- Returns the number of elements starting from `lo` that satisfy the given upper bound. -/
  size (lo : α) : Nat

/--
This typeclass ensures that a `RangeSize` instance returns the correct size for all ranges.
-/
class LawfulHasSize (α : Type u) [UpwardEnumerable α] [HasSize α] where
  /--
  If the smallest value in the range satisfies the upper bound and has no successor, the size is
  one.
  -/
  size_eq_one_of_succ?_eq_none (lo : α)
      (h : UpwardEnumerable.succ? lo = none) :
      HasSize.size lo = 1
  /--
  If the smallest value in the range satisfies the upper bound and has a successor, the size is
  one larger than the size of the range starting at the successor. -/
  size_eq_succ_of_succ?_eq_some (lo lo' : α)
      (h : UpwardEnumerable.succ? lo = some lo') :
      HasSize.size lo = HasSize.size lo' + 1

export LawfulHasSize (size_eq_one_of_succ?_eq_none size_eq_succ_of_succ?_eq_some)

theorem size_pos {α : Type u}
    [LT α] [UpwardEnumerable α] [HasSize α] [LawfulHasSize α]
    {lo : α} :
    HasSize.size lo > 0 := by
  open Classical in
  match hs : UpwardEnumerable.succ? lo with
  | none => simp [LawfulHasSize.size_eq_one_of_succ?_eq_none (h := hs)]
  | some b => simp [LawfulHasSize.size_eq_succ_of_succ?_eq_some (h := hs)]

end Rxi

namespace Rcc

variable {α : Type u} {r : Rcc α} {lo hi a : α}

/--
Checks whether the range contains any value.

This function returns a meaningful value for all range types defined by the standard library
and for all range types that satisfy the properties encoded in the `LawfulUpwardEnumerable`,
`LawfulUpwardEnumerableLowerBound` and `LawfulUpwardEnumerableUpperBound` typeclasses.
-/
@[inline]
def isEmpty [LE α] [DecidableLE α] [UpwardEnumerable α]
    (r : Rcc α) : Bool :=
  ¬ r.lower ≤ r.upper

theorem mem_iff [LE α] {r : Rcc α} {a : α} :
    a ∈ r ↔ r.lower ≤ a ∧ a ≤ r.upper :=
  Iff.rfl

theorem lower_le_of_mem [LE α] (h : a ∈ r) : r.lower ≤ a :=
  h.1

theorem le_upper_of_mem [LE α] (h : a ∈ r) : a ≤ r.upper :=
  h.2

end Rcc

namespace Rco

variable {α : Type u} {r : Rco α} {lo hi a : α}

/--
Checks whether the range contains any value.

This function returns a meaningful value for all range types defined by the standard library
and for all range types that satisfy the properties encoded in the `LawfulUpwardEnumerable`,
`LawfulUpwardEnumerableLowerBound` and `LawfulUpwardEnumerableUpperBound` typeclasses.
-/
@[inline]
def isEmpty [LT α] [DecidableLT α] [UpwardEnumerable α] (r : Rco α) : Bool :=
  ¬ r.lower < r.upper

theorem mem_iff [LE α] [LT α] :
    a ∈ r ↔ r.lower ≤ a ∧ a < r.upper :=
  Iff.rfl

theorem lower_le_of_mem [LE α] [LT α] (h : a ∈ r) : r.lower ≤ a :=
  h.1

theorem lt_upper_of_mem [LE α] [LT α] (h : a ∈ r) : a < r.upper :=
  h.2

theorem Internal.get_elem_helper_upper_open [LE α] [LT α] (h₁ : a ∈ r) (h₂ : r.upper = hi) :
    a < hi :=
  h₂ ▸ r.lt_upper_of_mem h₁

end Rco

namespace Rci

variable {α : Type u} {r : Rci α} {lo a : α}

/--
Checks whether the range contains any value.

This function returns a meaningful value for all range types defined by the standard library
and for all range types that satisfy the properties encoded in the `LawfulUpwardEnumerable`,
`LawfulUpwardEnumerableLowerBound` and `LawfulUpwardEnumerableUpperBound` typeclasses.
-/
@[inline]
def isEmpty [UpwardEnumerable α] (_ : Rci α) : Bool :=
  false

theorem mem_iff [LE α] :
    a ∈ r ↔ r.lower ≤ a :=
  Iff.rfl

theorem lower_le_of_mem [LE α] (h : a ∈ r) : r.lower ≤ a :=
  h

end Rci

namespace Roc

variable {α : Type u} {r : Roc α} {lo hi a : α}

/--
Checks whether the range contains any value.

This function returns a meaningful value for all range types defined by the standard library
and for all range types that satisfy the properties encoded in the `LawfulUpwardEnumerable`,
`LawfulUpwardEnumerableLowerBound` and `LawfulUpwardEnumerableUpperBound` typeclasses.
-/
@[inline]
def isEmpty [LT α] [DecidableLT α] [UpwardEnumerable α]
    (r : Roc α) : Bool :=
  ¬ r.lower < r.upper

theorem mem_iff [LE α] [LT α] {r : Roc α} {a : α} :
    a ∈ r ↔ r.lower < a ∧ a ≤ r.upper :=
  Iff.rfl

theorem lower_le_of_mem [LE α] [LT α] (h : a ∈ r) : r.lower < a :=
  h.1

theorem le_upper_of_mem [LE α] [LT α] (h : a ∈ r) : a ≤ r.upper :=
  h.2

end Roc

namespace Roo

variable {α : Type u} {r : Roo α} {lo hi a : α}

/--
Checks whether the range contains any value.

This function returns a meaningful value for all range types defined by the standard library
and for all range types that satisfy the properties encoded in the `LawfulUpwardEnumerable`,
`LawfulUpwardEnumerableLowerBound` and `LawfulUpwardEnumerableUpperBound` typeclasses.
-/
@[inline]
def isEmpty [LT α] [DecidableLT α] [UpwardEnumerable α] (r : Roo α) : Bool :=
  ∀ a, UpwardEnumerable.succ? r.lower = some a → ¬ a < r.upper

theorem mem_iff [LT α] :
    a ∈ r ↔ r.lower < a ∧ a < r.upper :=
  Iff.rfl

theorem lower_le_of_mem [LT α] (h : a ∈ r) : r.lower < a :=
  h.1

theorem lt_upper_of_mem [LT α] (h : a ∈ r) : a < r.upper :=
  h.2

theorem Internal.get_elem_helper_upper_open [LE α] [LT α] (h₁ : a ∈ r) (h₂ : r.upper = hi) :
    a < hi :=
  h₂ ▸ r.lt_upper_of_mem h₁

end Roo

namespace Roi

variable {α : Type u} {r : Roi α} {lo a : α}

/--
Checks whether the range contains any value.

This function returns a meaningful value for all range types defined by the standard library
and for all range types that satisfy the properties encoded in the `LawfulUpwardEnumerable`,
`LawfulUpwardEnumerableLowerBound` and `LawfulUpwardEnumerableUpperBound` typeclasses.
-/
@[inline]
def isEmpty [LT α] [DecidableLT α] [UpwardEnumerable α] (r : Roi α) : Bool :=
  UpwardEnumerable.succ? r.lower |>.isNone

theorem mem_iff [LT α] :
    a ∈ r ↔ r.lower < a :=
  Iff.rfl

theorem lower_le_of_mem [LT α] (h : a ∈ r) : r.lower < a :=
  h

end Roi

namespace Ric

variable {α : Type u} {r : Ric α} {hi a : α}

/--
Checks whether the range contains any value.

This function returns a meaningful value for all range types defined by the standard library
and for all range types that satisfy the properties encoded in the `LawfulUpwardEnumerable`,
`LawfulUpwardEnumerableLowerBound` and `LawfulUpwardEnumerableUpperBound` typeclasses.
-/
@[inline]
def isEmpty [UpwardEnumerable α] (_ : Ric α) : Bool :=
  false

theorem mem_iff [LE α] : a ∈ r ↔ a ≤ r.upper :=
  Iff.rfl

theorem le_upper_of_mem [LE α] [LT α] (h : a ∈ r) : a ≤ r.upper :=
  h

end Ric

namespace Rio

variable {α : Type u} {r : Rio α} {hi a : α}

/--
Checks whether the range contains any value.

This function returns a meaningful value for all range types defined by the standard library
and for all range types that satisfy the properties encoded in the `LawfulUpwardEnumerable`,
`LawfulUpwardEnumerableLowerBound` and `LawfulUpwardEnumerableUpperBound` typeclasses.
-/
@[inline]
def isEmpty [LT α] [DecidableLT α] [UpwardEnumerable α] [Least? α] (r : Rio α) : Bool :=
  ∀ a, Least?.least? (α := α) = some a → ¬ a < r.upper

theorem mem_iff [LT α] : a ∈ r ↔ a < r.upper :=
  Iff.rfl

theorem lt_upper_of_mem [LT α] (h : a ∈ r) : a < r.upper :=
  h

theorem Internal.get_elem_helper_upper_open [LE α] [LT α] (h₁ : a ∈ r) (h₂ : r.upper = hi) :
    a < hi :=
  h₂ ▸ r.lt_upper_of_mem h₁

end Rio

namespace Rii

variable {α : Type u} {r : Rii α} {a : α}

/--
Checks whether the range contains any value.

This function returns a meaningful value for all range types defined by the standard library
and for all range types that satisfy the properties encoded in the `LawfulUpwardEnumerable`,
`LawfulUpwardEnumerableLowerBound` and `LawfulUpwardEnumerableUpperBound` typeclasses.
-/
@[inline]
def isEmpty [Least? α] (_ : Rii α) : Bool :=
  (Least?.least? (α := α)).isNone

theorem mem : a ∈ r :=
  True.intro

end Rii

macro_rules
  | `(tactic| get_elem_tactic_extensible) =>
    `(tactic|
      first
        -- This is a relatively rigid check. See `Init.Data.Range.Polymorphic.GetElemTactic`
        -- for a second one that is more flexible.
        -- Note: This one is not *strictly* inferior. This one is better able to look under
        -- reducible terms. The other tactic needs special handling for `Vector.size` to work
        -- around that fact that `omega` does not reduce terms.
        | apply Std.Rco.Internal.get_elem_helper_upper_open ‹_› (by trivial)
        | apply Std.Roo.Internal.get_elem_helper_upper_open ‹_› (by trivial)
        | apply Std.Rio.Internal.get_elem_helper_upper_open ‹_› (by trivial)
        | done)

end Std
