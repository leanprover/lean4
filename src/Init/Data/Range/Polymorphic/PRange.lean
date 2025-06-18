/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Init.Core
import Init.NotationExtra
import Init.Data.Iterators.Consumers
import Init.Data.Range.Polymorphic.UpwardEnumerable

open Std.Iterators

namespace Std.PRange

/--
The shape of a range's upper or lower bound: `open`, `closed` or `unbounded`.
-/
inductive BoundShape where
  /--
  An open upper (or lower) bound of this shape requires elements of a range to be less than
  (or greater than) the bound, excluding the bound itself.
  -/
  | «open» : BoundShape
  /--
  A closed upper (or lower) bound of this shape requires elements of a range to be less than or equal
  (or greater than or equal) to the bound.
  -/
  | closed : BoundShape
  /--
  This bound shape signifies the absence of a range bound, so that the range is unbounded in at
  least one direction.
  -/
  | unbounded : BoundShape

/-- The shape of a range, consisting of the shape of its upper and lower bounds. -/
structure RangeShape where
  /-- The shape of the range's lower bound. -/
  lower : BoundShape
  /-- The shape of the range's upper bound. -/
  upper : BoundShape

/--
An upper or lower bound in `α` of the given shape.
-/
abbrev Bound (shape : BoundShape) (α : Type u) : Type u :=
  match shape with
  | .open | .closed => α
  | .unbounded => PUnit

/--
A range of elements of some type `α`. It is characterized by its upper and lower bounds, which
may be inclusive, exclusive or absent.

* `a..b` contains all elements between `a` and `b`, including `a`.
* `a<..b` contains all elements between `a` and `b`, excluding `a`.
* `a..<b` contains all elements between `a` and `b`, excluding `b`.
* `a<..<b` contains all elements between `a` and `b`, excluding both `a` and `b`.
* `..b` contains all elements below `b`, including `b`.
* `..<b` contains all elements below `b`, excluding `b`.
* `a..` contains all elements above `a`, including `a`.
* `a<..` contains all elements above `a`, excluding `a`.
* `..` contains all elements of `α`.
-/
structure _root_.Std.PRange (shape : RangeShape) (α : Type u) where
  /-- The lower bound of the range. -/
  lower : Bound shape.lower α
  /-- The upper bound of the range. -/
  upper : Bound shape.upper α

syntax:max (term ",," term) : term
syntax:max (",," term) : term
syntax:max (term ",,") : term
syntax:max (",,") : term
syntax:max (term "<,," term) : term
syntax:max (term "<,,") : term
syntax:max (term ",,<" term) : term
syntax:max (",,<" term) : term
syntax:max (term "<,,<" term) : term

macro_rules
  | `($a,,$b) => ``(PRange.mk (shape := RangeShape.mk BoundShape.closed BoundShape.closed) $a $b)
  | `(,,$b) => ``(PRange.mk (shape := RangeShape.mk BoundShape.unbounded BoundShape.closed) PUnit.unit $b)
  | `($a,,) => ``(PRange.mk (shape := RangeShape.mk BoundShape.closed BoundShape.unbounded) $a PUnit.unit)
  | `(,,) => ``(PRange.mk (shape := RangeShape.mk BoundShape.unbounded BoundShape.unbounded) PUnit.unit PUnit.unit)
  | `($a<,,$b) => ``(PRange.mk (shape := RangeShape.mk BoundShape.open BoundShape.closed) $a $b)
  | `($a<,,) => ``(PRange.mk (shape := RangeShape.mk BoundShape.open BoundShape.unbounded) $a PUnit.unit)
  | `($a,,<$b) => ``(PRange.mk (shape := RangeShape.mk BoundShape.closed BoundShape.open) $a $b)
  | `(,,<$b) => ``(PRange.mk (shape := RangeShape.mk BoundShape.unbounded BoundShape.open) PUnit.unit $b)
  | `($a<,,<$b) => ``(PRange.mk (shape := RangeShape.mk BoundShape.open BoundShape.open) $a $b)

/--
This typeclass provides decidable lower bound checks of the given shape.

Instances are automatically provided in the following cases:

* `shape` is `open` and there is an `LT α` instance
* `shape` is `closed` and there is an `LE α` instance
* `shape` is `.unbounded`
-/
class SupportsLowerBound (shape : BoundShape) (α : Type u) where
  IsSatisfied : Bound shape α → α → Prop
  decidableSatisfiesLowerBound : DecidableRel IsSatisfied := by infer_instance

instance : SupportsLowerBound .unbounded α where
  IsSatisfied _ _ := True

/--
This typeclass provides decidable upper bound checks of the given shape.

Instances are automatically provided in the following cases:

* `shape` is `open` and there is an `LT α` instance
* `shape` is `closed` and there is an `LE α` instance
* `shape` is `.unbounded`
-/
class SupportsUpperBound (shape : BoundShape) (α : Type u) where
  IsSatisfied : Bound shape α → α → Prop
  decidableSatisfiesUpperBound : DecidableRel IsSatisfied := by infer_instance

instance : SupportsUpperBound .unbounded α where
  IsSatisfied _ _ := True

instance [i : SupportsLowerBound shape α] : DecidableRel i.IsSatisfied :=
  i.decidableSatisfiesLowerBound

instance [i : SupportsUpperBound shape α] : DecidableRel i.IsSatisfied :=
  i.decidableSatisfiesUpperBound

instance [SupportsLowerBound sl α] [SupportsUpperBound su α] :
    Membership α (PRange ⟨sl, su⟩ α) where
  mem r a := SupportsLowerBound.IsSatisfied r.lower a ∧ SupportsUpperBound.IsSatisfied r.upper a

instance [SupportsLowerBound sl α] [SupportsUpperBound su α] (r : PRange ⟨sl, su⟩ α) :
    Decidable (a ∈ r) :=
  inferInstanceAs <| Decidable (_ ∧ _)

/--
This typeclass ensures that ranges of the given shape are always finite. This is a prerequisite
for many functions and instances, such as `PRange.toList` or `ForIn'`.
-/
class HasFiniteRanges (shape α) [SupportsUpperBound shape α] : Prop where
  mem_of_satisfiesUpperBound (u : Bound shape α) :
    ∃ enumeration : List α, (a : α) → SupportsUpperBound.IsSatisfied u a → a ∈ enumeration

/--
This typeclass will usually be used together with `UpwardEnumerable α`. It provides the starting
point from which to enumerate all the values above the given lower bound.

Instances are automatically generated in the following cases:

* `lowerBoundShape` is `.closed`
* `lowerBoundShape` is `.open` and there is an `UpwardEnumerable α` instance
* `lowerBoundShape` is `.unbounded` and there is a `Least? α` instance
-/
class BoundedUpwardEnumerable (lowerBoundShape : BoundShape) (α : Type u) where
  init? : Bound lowerBoundShape α → Option α

/--
This typeclass ensures that the lower bound predicate from `SupportsLowerBound sl α`
can be characterized in terms of `UpwardEnumerable α` and `BoundedUpwardEnumerable sl α`.
-/
class LawfulUpwardEnumerableLowerBound (sl α) [UpwardEnumerable α]
    [SupportsLowerBound sl α] [BoundedUpwardEnumerable sl α] where
  /--
  An element `a` satisfies the lower bound `l` if and only if it is
  `BoundedUpwardEnumerable.init? l` or one of its transitive successors.
  -/
  isSatisfied_iff (a : α) (l : Bound sl α) :
    SupportsLowerBound.IsSatisfied l a ↔
      ∃ init, BoundedUpwardEnumerable.init? l = some init ∧ UpwardEnumerable.le init a

/--
This typeclass ensures that if `b` is a transitive successor of `a` and `b` satisfies an upper bound
of the given shape, then `a` also satisfies the upper bound.
-/
class LawfulUpwardEnumerableUpperBound (su α) [UpwardEnumerable α] [SupportsUpperBound su α] where
  /--
  If `b` is a transitive successor of `a` and `b` satisfies a certain upper bound, then
  `a` also satisfies the upper bound.
  -/
  isSatisfied_of_le (u : Bound su α) (a b : α) :
    SupportsUpperBound.IsSatisfied u b → UpwardEnumerable.le a b → SupportsUpperBound.IsSatisfied u a

theorem LawfulUpwardEnumerableLowerBound.isSatisfied_of_le [SupportsLowerBound sl α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerableLowerBound sl α]
    (l : Bound sl α) (a b : α)
    (ha : SupportsLowerBound.IsSatisfied l a) (hle : UpwardEnumerable.le a b) :
    SupportsLowerBound.IsSatisfied l b := by
  rw [LawfulUpwardEnumerableLowerBound.isSatisfied_iff] at ⊢ ha
  obtain ⟨init, hi, ha⟩ := ha
  exact ⟨init, hi, UpwardEnumerable.le_trans ha hle⟩

instance [LT α] [DecidableLT α] : SupportsLowerBound .open α where
  IsSatisfied bound a := bound < a

instance [LT α] [DecidableLT α] : SupportsUpperBound .open α where
  IsSatisfied bound a := a < bound

instance [LE α] [DecidableLE α] : SupportsLowerBound .closed α where
  IsSatisfied bound a := bound ≤ a

instance [LE α] [DecidableLE α] : SupportsUpperBound .closed α where
  IsSatisfied bound a := a ≤ bound

instance [Least? α] : BoundedUpwardEnumerable .unbounded α where
  init? _ := Least?.least?

instance [UpwardEnumerable α] : BoundedUpwardEnumerable .open α where
  init? lower := UpwardEnumerable.succ? lower

instance : BoundedUpwardEnumerable .closed α where
  init? lower := some lower

end Std.PRange
