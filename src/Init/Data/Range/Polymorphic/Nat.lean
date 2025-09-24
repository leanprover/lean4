/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Init.Data.Nat.Lemmas
public import Init.Data.Nat.Order
public import Init.Data.Range.Polymorphic.Instances
public import Init.Data.Order.Classes
public import Init.Data.Order.Lemmas

public section

open Std PRange

namespace Std.PRange

instance : UpwardEnumerable Nat where
  succ? n := some (n + 1)
  succMany? k n := some (n + k)

instance : Least? Nat where
  least? := some 0

instance : LawfulUpwardEnumerableLeast? Nat where
  least?_le a := by
    simpa [Least?.least?] using ⟨a, by simp [UpwardEnumerable.succMany?]⟩

instance : LawfulUpwardEnumerableLE Nat where
  le_iff a b := by
    constructor
    · intro h
      exact ⟨b - a, by simp [UpwardEnumerable.succMany?, Nat.add_sub_cancel' h]⟩
    · rintro ⟨n, hn⟩
      simp only [UpwardEnumerable.succMany?, Option.some.injEq] at hn
      rw [← hn]
      exact Nat.le_add_right _ _

instance : LawfulUpwardEnumerable Nat where
  succMany?_zero := by simp [UpwardEnumerable.succMany?]
  succMany?_succ? := by simp [UpwardEnumerable.succMany?, UpwardEnumerable.succ?, Nat.add_assoc]
  ne_of_lt a b hlt := by
    have hn := hlt.choose_spec
    simp only [UpwardEnumerable.succMany?, Option.some.injEq] at hn
    omega

instance : LawfulUpwardEnumerableLT Nat := inferInstance
instance : LawfulUpwardEnumerableLowerBound .closed Nat := inferInstance
instance : LawfulUpwardEnumerableUpperBound .closed Nat := inferInstance
instance : LawfulUpwardEnumerableLowerBound .open Nat := inferInstance
instance : LawfulUpwardEnumerableUpperBound .open Nat := inferInstance
instance : LawfulUpwardEnumerableLowerBound .unbounded Nat := inferInstance
instance : LawfulUpwardEnumerableUpperBound .unbounded Nat := inferInstance

instance : InfinitelyUpwardEnumerable Nat where
  isSome_succ? a := by simp [UpwardEnumerable.succ?]

instance : RangeSize .closed Nat where
  size bound a := bound + 1 - a

instance : RangeSize .open Nat := .openOfClosed

instance : LawfulRangeSize .closed Nat where
  size_eq_zero_of_not_isSatisfied upperBound init hu := by
    simp only [SupportsUpperBound.IsSatisfied, RangeSize.size] at hu ⊢
    omega
  size_eq_one_of_succ?_eq_none upperBound init hu h := by
    simp only [UpwardEnumerable.succ?] at h
    cases h
  size_eq_succ_of_succ?_eq_some upperBound init hu h := by
    simp only [SupportsUpperBound.IsSatisfied, RangeSize.size, UpwardEnumerable.succ?,
      Option.some.injEq] at hu h ⊢
    omega

instance : LawfulRangeSize .open Nat := inferInstance
instance : HasFiniteRanges .closed Nat := inferInstance
instance : HasFiniteRanges .open Nat := inferInstance
instance : LinearlyUpwardEnumerable Nat := inferInstance

/-!
The following instances are used for the implementation of array slices a.k.a. `Subarray`.
See also `Init.Data.Slice.Array`.
-/

instance : ClosedOpenIntersection ⟨.open, .open⟩ Nat where
  intersection r s := PRange.mk (max (r.lower + 1) s.lower) (min r.upper s.upper)

example (h : b + 1 ≤ a) : b < a := by omega

instance : LawfulClosedOpenIntersection ⟨.open, .open⟩ Nat where
  mem_intersection_iff {a r s} := by
    simp only [ClosedOpenIntersection.intersection, Membership.mem, SupportsLowerBound.IsSatisfied,
      SupportsUpperBound.IsSatisfied, Nat.max_le, Nat.lt_min, Bound]
    omega

instance : ClosedOpenIntersection ⟨.open, .closed⟩ Nat where
  intersection r s := PRange.mk (max (r.lower + 1) s.lower) (min (r.upper + 1) s.upper)

instance : LawfulClosedOpenIntersection ⟨.open, .closed⟩ Nat where
  mem_intersection_iff {a r s} := by
    simp only [ClosedOpenIntersection.intersection, Membership.mem, SupportsLowerBound.IsSatisfied,
      SupportsUpperBound.IsSatisfied, Nat.max_le, Nat.lt_min, Bound]
    omega

instance : ClosedOpenIntersection ⟨.open, .unbounded⟩ Nat where
  intersection r s := PRange.mk (max (r.lower + 1) s.lower) s.upper

instance : LawfulClosedOpenIntersection ⟨.open, .unbounded⟩ Nat where
  mem_intersection_iff {a r s} := by
    simp only [Membership.mem, SupportsLowerBound.IsSatisfied, Bound,
      ClosedOpenIntersection.intersection, Nat.max_le, SupportsUpperBound.IsSatisfied, and_true]
    omega

instance : ClosedOpenIntersection ⟨.closed, .open⟩ Nat where
  intersection r s := PRange.mk (max r.lower s.lower) (min r.upper s.upper)

instance : LawfulClosedOpenIntersection ⟨.closed, .open⟩ Nat where
  mem_intersection_iff {a r s} := by
    simp only [ClosedOpenIntersection.intersection, Membership.mem, SupportsLowerBound.IsSatisfied,
      SupportsUpperBound.IsSatisfied, Nat.max_le, Nat.lt_min, Bound]
    omega

instance : ClosedOpenIntersection ⟨.closed, .closed⟩ Nat where
  intersection r s := PRange.mk (max r.lower s.lower) (min (r.upper + 1) s.upper)

instance : LawfulClosedOpenIntersection ⟨.closed, .closed⟩ Nat where
  mem_intersection_iff {a r s} := by
    simp only [ClosedOpenIntersection.intersection, Membership.mem, SupportsLowerBound.IsSatisfied,
      SupportsUpperBound.IsSatisfied, Nat.max_le, Nat.lt_min, Bound]
    omega

instance : ClosedOpenIntersection ⟨.closed, .unbounded⟩ Nat where
  intersection r s := PRange.mk (max r.lower s.lower) s.upper

instance : LawfulClosedOpenIntersection ⟨.closed, .unbounded⟩ Nat where
  mem_intersection_iff {a r s} := by
    simp only [Membership.mem, SupportsLowerBound.IsSatisfied, Bound,
      ClosedOpenIntersection.intersection, Nat.max_le, SupportsUpperBound.IsSatisfied, and_true]
    omega

instance : ClosedOpenIntersection ⟨.unbounded, .open⟩ Nat where
  intersection r s := PRange.mk s.lower (min r.upper s.upper)

instance : LawfulClosedOpenIntersection ⟨.unbounded, .open⟩ Nat where
  mem_intersection_iff {a r s} := by
    simp only [Membership.mem, SupportsLowerBound.IsSatisfied, Bound,
      ClosedOpenIntersection.intersection, SupportsUpperBound.IsSatisfied, true_and]
    omega

instance : ClosedOpenIntersection ⟨.unbounded, .closed⟩ Nat where
  intersection r s := PRange.mk s.lower (min (r.upper + 1) s.upper)

instance : LawfulClosedOpenIntersection ⟨.unbounded, .closed⟩ Nat where
  mem_intersection_iff {a r s} := by
    simp only [Membership.mem, SupportsLowerBound.IsSatisfied, Bound,
      ClosedOpenIntersection.intersection, SupportsUpperBound.IsSatisfied, true_and]
    omega

instance : ClosedOpenIntersection ⟨.unbounded, .unbounded⟩ Nat where
  intersection _ s := s

instance : LawfulClosedOpenIntersection ⟨.unbounded, .unbounded⟩ Nat where
  mem_intersection_iff {a r s} := by
    simp [Membership.mem, SupportsLowerBound.IsSatisfied, Bound,
      ClosedOpenIntersection.intersection, SupportsUpperBound.IsSatisfied]

end Std.PRange
