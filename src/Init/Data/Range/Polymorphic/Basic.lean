/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Range.Polymorphic.PRange

public section

namespace Std.PRange

/--
This typeclass provides support for the `PRange.size` function.

The returned size should be equal to the number of elements returned by `toList`. This condition
is captured by the typeclass `LawfulRangeSize`.
-/
class RangeSize (shape : BoundShape) (α : Type u) where
  /-- Returns the number of elements starting from `init` that satisfy the given upper bound. -/
  size : (upperBound : Bound shape α) → (init : α) → Nat

/--
This typeclass ensures that a `RangeSize` instance returns the correct size for all ranges.
-/
class LawfulRangeSize (su : BoundShape) (α : Type u) [UpwardEnumerable α]
    [SupportsUpperBound su α] [RangeSize su α]
    [LawfulUpwardEnumerable α] [HasFiniteRanges su α] where
  /-- If the smallest value in the range is beyond the upper bound, the size is zero. -/
  size_eq_zero_of_not_satisfied (upperBound : Bound su α) (init : α)
      (h : ¬ SupportsUpperBound.IsSatisfied upperBound init) :
      RangeSize.size upperBound init = 0
  /--
  If the smallest value in the range satisfies the upper bound and has no successor, the size is
  one.
  -/
  size_eq_one_of_succ?_eq_none (upperBound : Bound su α) (init : α)
      (h : SupportsUpperBound.IsSatisfied upperBound init)
      (h' : UpwardEnumerable.succ? init = none) :
      RangeSize.size upperBound init = 1
  /--
  If the smallest value in the range satisfies the upper bound and has a successor, the size is
  one larger than the size of the range starting at the successor. -/
  size_eq_succ_of_succ?_eq_some (upperBound : Bound su α) (init : α)
      (h : SupportsUpperBound.IsSatisfied upperBound init)
      (h' : UpwardEnumerable.succ? init = some a) :
      RangeSize.size upperBound init = RangeSize.size upperBound a + 1

/--
Checks whether the range contains any value.

This function returns a meaningful value for all range types defined by the standard library
and for all range types that satisfy the properties encoded in the `LawfulUpwardEnumerable`,
`LawfulUpwardEnumerableLowerBound` and `LawfulUpwardEnumerableUpperBound` typeclasses.
-/
@[always_inline, inline]
def isEmpty {sl su α} [UpwardEnumerable α] [BoundedUpwardEnumerable sl α]
    [SupportsUpperBound su α] (r : PRange ⟨sl, su⟩ α) : Bool :=
  (BoundedUpwardEnumerable.init? r.lower).all (! SupportsUpperBound.IsSatisfied r.upper ·)

theorem le_upper_of_mem {sl α} [LE α] [DecidableLE α] [SupportsLowerBound sl α]
    {a : α} {r : PRange ⟨sl, .closed⟩ α} (h : a ∈ r) : a ≤ r.upper :=
  h.2

theorem lt_upper_of_mem {sl α} [LT α] [DecidableLT α] [SupportsLowerBound sl α]
    {a : α} {r : PRange ⟨sl, .open⟩ α} (h : a ∈ r) : a < r.upper :=
  h.2

theorem lower_le_of_mem {su α} [LE α] [DecidableLE α] [SupportsUpperBound su α]
    {a : α} {r : PRange ⟨.closed, su⟩ α} (h : a ∈ r) : r.lower ≤ a :=
  h.1

theorem lower_lt_of_mem {su α} [LT α] [DecidableLT α] [SupportsUpperBound su α]
    {a : α} {r : PRange ⟨.open, su⟩ α} (h : a ∈ r) : r.lower < a :=
  h.1

theorem Internal.get_elem_helper_upper_open {sl α} [SupportsLowerBound sl α] [LT α] [DecidableLT α]
    {a n : α} {r : PRange ⟨sl, .open⟩ α} (h₁ : a ∈ r) (h₂ : r.upper = n) :
    a < n := h₂ ▸ r.lt_upper_of_mem h₁

macro_rules
  | `(tactic| get_elem_tactic_extensible) =>
    `(tactic|
      first
        | apply Std.PRange.Internal.get_elem_helper_upper_open ‹_› (by trivial)
        | done)

end Std.PRange
