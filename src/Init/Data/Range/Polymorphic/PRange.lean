/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Core
public import Init.Data.Range.Polymorphic.UpwardEnumerable

public section

namespace Std

open PRange

/--
A range of elements of `α` with closed lower and upper bounds.

`a...=b` is the range of all values greater than or equal to `a` and less than or equal to `b`.
This is notation for `Rcc.mk a b`.
-/
structure Rcc (α : Type u) where
  lower : α
  upper : α

/--
A range of elements of `α` with a closed lower bound and an open upper bound.

`a...b` or `a...<b` is the range of all values greater than or equal to `a` and less than `b`.
This is notation for `Rco.mk a b`.
-/
structure Rco (α : Type u) where
  lower : α
  upper : α

/--
An upward-unbounded range of elements of `α` with a closed lower bound.

`a...*` is the range of all values greater than or equal to `a`.
This is notation for `Rci.mk a b`.
-/
structure Rci (α : Type u) where
  lower : α

structure Roc (α : Type u) where
  lower : α
  upper : α

structure Roo (α : Type u) where
  lower : α
  upper : α

structure Roi (α : Type u) where
  lower : α

structure Ric (α : Type u) where
  upper : α

structure Rio (α : Type u) where
  upper : α

structure Rii (α : Type u) where

/-- `a...*` is the range of elements greater than or equal to `a`. See also `Std.Rci`. -/
syntax:max (term "...*") : term
/-- `*...*` is the range that is unbounded in both directions. See also `Std.Rii`. -/
syntax:max ("*...*") : term
/-- `a<...*` is the range of elements greater than `a`. See also `Std.Roi`. -/
syntax:max (term "<...*") : term
/--
`a...<b` is the range of elements greater than or equal to `a` and less than `b`.
See also `Std.Rco`.
-/
syntax:max (term "...<" term) : term
/--
`a...b` is the range of elements greater than or equal to `a` and less than `b`.
See also `Std.Rco`.
-/
syntax:max (term "..." term) : term
/-- `*...<b` is the range of elements less than `b`. See also `Std.Rio`. -/
syntax:max ("*...<" term) : term
/-- `*...b` is the range of elements less than `b`. See also `Std.Rio`. -/
syntax:max ("*..." term) : term
/--
`a<...<b` is the range of elements greater than `a` and less than `b`.
See also `Std.Roo`.
-/
syntax:max (term "<...<" term) : term
/--
`a<...b` is the range of elements greater than `a` and less than `b`.
See also `Std.Roo`.
-/
syntax:max (term "<..." term) : term
/--
`a...=b` is the range of elements greater than or equal to `a` and less than or equal to `b`.
See also `Std.Rcc`.
-/
syntax:max (term "...=" term) : term
/-- `*...=b` is the range of elements less than or equal to `b`. See also `Std.Ric`. -/
syntax:max ("*...=" term) : term
/--
`a<...=b` is the range of elements greater than `a` and less than or equal to `b`.
See also `Std.Roc`.
-/
syntax:max (term "<...=" term) : term

macro_rules
  | `($a...=$b) => ``(Rcc.mk $a $b)
  | `(*...=$b) => ``(Ric.mk $b)
  | `($a...*) => ``(Rci.mk $a)
  | `(*...*) => ``(Rii.mk)
  | `($a<...=$b) => ``(Roc.mk $a $b)
  | `($a<...*) => ``(Roi.mk $a)
  | `($a...<$b) => ``(Rco.mk $a $b)
  | `($a...$b) => ``(Rco.mk $a $b)
  | `(*...<$b) => ``(Rio.mk $b)
  | `(*...$b) => ``(Rio.mk $b)
  | `($a<...<$b) => ``(Roo.mk $a $b)
  | `($a<...$b) => ``(Roo.mk $a $b)

/--
TODO: update
This typeclass ensures that ranges with the given shape of upper bounds are always finite.
This is a prerequisite for many functions and instances, such as `PRange.toList` or `ForIn'`.
-/
class Rxc.IsAlwaysFinite (α : Type u) [UpwardEnumerable α] [LE α] : Prop where
  finite (init : α) (hi : α) :
    ∃ n, (UpwardEnumerable.succMany? n init).elim True (¬ · ≤ hi)

/--
TODO: update
This typeclass ensures that ranges with the given shape of upper bounds are always finite.
This is a prerequisite for many functions and instances, such as `PRange.toList` or `ForIn'`.
-/
class Rxo.IsAlwaysFinite (α : Type u) [UpwardEnumerable α] [LT α] : Prop where
  finite (init : α) (hi : α) :
    ∃ n, (UpwardEnumerable.succMany? n init).elim True (¬ · < hi)

/--
TODO: update
This typeclass ensures that ranges with the given shape of upper bounds are always finite.
This is a prerequisite for many functions and instances, such as `PRange.toList` or `ForIn'`.
-/
class Rxi.IsAlwaysFinite (α : Type u) [UpwardEnumerable α] : Prop where
  finite (init : α) : ∃ n, UpwardEnumerable.succMany? n init = none

namespace Rcc

variable {α : Type u} {r : Rcc α} {a : α}

instance [LE α] : Membership α (Rcc α) where
  mem r a := r.lower ≤ a ∧ a ≤ r.upper

instance [LE α] [DecidableLE α] : Decidable (a ∈ r) := inferInstanceAs (Decidable (_ ∧ _))

end Rcc

namespace Rco

variable {α : Type u} {r : Rco α} {a : α}

instance [LE α] [LT α] : Membership α (Rco α) where
  mem r a := r.lower ≤ a ∧ a < r.upper

instance [LE α] [DecidableLE α] [LT α] [DecidableLT α] :
    Decidable (a ∈ r) := inferInstanceAs (Decidable (_ ∧ _))

end Rco

namespace Rci

variable {α : Type u} {r : Rci α} {a : α}

instance [LE α] : Membership α (Rci α) where
  mem r a := r.lower ≤ a

instance [LE α] [DecidableLE α] :
    Decidable (a ∈ r) := inferInstanceAs (Decidable (_ ≤ _))

end Rci

namespace Roc

variable {α : Type u} {r : Roc α} {a : α}

instance [LE α] [LT α] : Membership α (Roc α) where
  mem r a := r.lower < a ∧ a ≤ r.upper

instance [LE α] [DecidableLE α] [LT α] [DecidableLT α] : Decidable (a ∈ r) :=
  inferInstanceAs (Decidable (_ ∧ _))

end Roc

namespace Roo

variable {α : Type u} {r : Roo α} {a : α}

instance [LT α] : Membership α (Roo α) where
  mem r a := r.lower < a ∧ a < r.upper

instance [LT α] [DecidableLT α] : Decidable (a ∈ r) := inferInstanceAs (Decidable (_ ∧ _))

end Roo

namespace Roi

variable {α : Type u} {r : Roi α} {a : α}

instance [LT α] : Membership α (Roi α) where
  mem r a := r.lower < a

instance [LT α] [DecidableLT α] : Decidable (a ∈ r) := inferInstanceAs (Decidable (_ < _))

end Roi

namespace Ric

variable {α : Type u} {r : Ric α} {a : α}

instance [LE α] : Membership α (Ric α) where
  mem r a := a ≤ r.upper

instance [LE α] [DecidableLE α] : Decidable (a ∈ r) := inferInstanceAs (Decidable (_ ≤ _))

end Ric

namespace Rio

variable {α : Type u} {r : Rio α} {a : α}

instance [LT α] : Membership α (Rio α) where
  mem r a := a < r.upper

instance [LT α] [DecidableLT α] : Decidable (a ∈ r) := inferInstanceAs (Decidable (_ < _))

end Rio

namespace Rii

variable {α : Type u} {r : Rii α} {a : α}

instance : Membership α (Rii α) where
  mem _ _ := True

instance : Decidable (a ∈ r) := inferInstanceAs (Decidable True)

end Rii

-- class HasFiniteRanges (shape α) [UpwardEnumerable α] [SupportsUpperBound shape α] : Prop where
--   finite (init : α) (u : Bound shape α) :
--     ∃ n, (UpwardEnumerable.succMany? n init).elim True (¬ SupportsUpperBound.IsSatisfied u ·)

-- /--
-- This typeclass will usually be used together with `UpwardEnumerable α`. It provides the starting
-- point from which to enumerate all the values above the given lower bound.

-- Instances are automatically generated in the following cases:

-- * `lowerBoundShape` is `.closed`
-- * `lowerBoundShape` is `.open` and there is an `UpwardEnumerable α` instance
-- * `lowerBoundShape` is `.unbounded` and there is a `Least? α` instance
-- -/
-- class BoundedUpwardEnumerable (lowerBoundShape : BoundShape) (α : Type u) where
--   init? : Bound lowerBoundShape α → Option α

-- attribute [simp] BoundedUpwardEnumerable.init?
-- export BoundedUpwardEnumerable (init?)

-- /--
-- This typeclass ensures that the lower bound predicate from `SupportsLowerBound sl α`
-- can be characterized in terms of `UpwardEnumerable α` and `BoundedUpwardEnumerable sl α`.
-- -/
-- class LawfulUpwardEnumerableLowerBound (sl α) [UpwardEnumerable α]
--     [SupportsLowerBound sl α] [BoundedUpwardEnumerable sl α] where
--   /--
--   An element `a` satisfies the lower bound `l` if and only if it is
--   `init? l` or one of its transitive successors.
--   -/
--   isSatisfied_iff (a : α) (l : Bound sl α) :
--     SupportsLowerBound.IsSatisfied l a ↔ ∃ init, init? l = some init ∧ UpwardEnumerable.LE init a

-- /--
-- This typeclass ensures that if `b` is a transitive successor of `a` and `b` satisfies an upper bound
-- of the given shape, then `a` also satisfies the upper bound.
-- -/
-- class LawfulUpwardEnumerableUpperBound (su α) [UpwardEnumerable α] [SupportsUpperBound su α] where
--   /--
--   If `b` is a transitive successor of `a` and `b` satisfies a certain upper bound, then
--   `a` also satisfies the upper bound.
--   -/
--   isSatisfied_of_le (u : Bound su α) (a b : α) :
--     SupportsUpperBound.IsSatisfied u b → UpwardEnumerable.LE a b → SupportsUpperBound.IsSatisfied u a

-- theorem LawfulUpwardEnumerableLowerBound.isSatisfied_of_le [SupportsLowerBound sl α]
--     [UpwardEnumerable α] [LawfulUpwardEnumerable α]
--     [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerableLowerBound sl α]
--     (l : Bound sl α) (a b : α)
--     (ha : SupportsLowerBound.IsSatisfied l a) (hle : UpwardEnumerable.LE a b) :
--     SupportsLowerBound.IsSatisfied l b := by
--   rw [LawfulUpwardEnumerableLowerBound.isSatisfied_iff] at ⊢ ha
--   obtain ⟨init, hi, ha⟩ := ha
--   exact ⟨init, hi, UpwardEnumerable.le_trans ha hle⟩

-- /--
-- This typeclass ensures that `SupportsUpperBound .closed α` and `UpwardEnumerable α` instances
-- are compatible.
-- -/
-- class LawfulClosedUpperBound (α : Type w) [SupportsUpperBound .closed α]
--     [UpwardEnumerable α] where
--   /--
--   A closed upper bound is satisfied for `a` if and only if it is greater than or equal to `a`
--   according to `UpwardEnumerable.LE`.
--   -/
--   isSatisfied_iff_le (u : Bound .closed α) (a : α) :
--     SupportsUpperBound.IsSatisfied u a ↔ UpwardEnumerable.LE a u

-- /--
-- This typeclass ensures that `SupportsUpperBound .open α` and `UpwardEnumerable α` instances
-- are compatible.
-- -/
-- class LawfulOpenUpperBound (α : Type w) [SupportsUpperBound .open α]
--     [UpwardEnumerable α] where
--   /--
--   An open upper bound is satisfied for `a` if and only if it is greater than to `a`
--   according to `UpwardEnumerable.LT`.
--   -/
--   isSatisfied_iff_le (u : Bound .open α) (a : α) :
--     SupportsUpperBound.IsSatisfied u a ↔ UpwardEnumerable.LT a u

-- /--
-- This typeclass ensures that according to `SupportsUpperBound .unbounded α`, every element is
-- in bounds.
-- -/
-- class LawfulUnboundedUpperBound (α : Type w) [SupportsUpperBound .unbounded α] where
--   /--
--   An unbounded upper bound is satisfied for every element.
--   -/
--   isSatisfied (u : Bound .unbounded α) (a : α) :
--     SupportsUpperBound.IsSatisfied u a

-- instance {α} [LT α] [DecidableLT α] : SupportsLowerBound .open α where
--   IsSatisfied bound a := bound < a

-- instance {α} [LT α] [DecidableLT α] : SupportsUpperBound .open α where
--   IsSatisfied bound a := a < bound

-- instance {α} [LE α] [DecidableLE α] : SupportsLowerBound .closed α where
--   IsSatisfied bound a := bound ≤ a

-- instance {α} [LE α] [DecidableLE α] : SupportsUpperBound .closed α where
--   IsSatisfied bound a := a ≤ bound

-- instance {α} [Least? α] : BoundedUpwardEnumerable .unbounded α where
--   init? _ := Least?.least?

-- instance {α} [UpwardEnumerable α] : BoundedUpwardEnumerable .open α where
--   init? lower := UpwardEnumerable.succ? lower

-- instance {α} : BoundedUpwardEnumerable .closed α where
--   init? lower := some lower

-- instance {α} [LE α] [DecidableLE α] [UpwardEnumerable α] [LawfulUpwardEnumerableLE α] :
--     LawfulClosedUpperBound α where
--   isSatisfied_iff_le u a := by simp [SupportsUpperBound.IsSatisfied, LawfulUpwardEnumerableLE.le_iff]

-- instance {α} [LT α] [DecidableLT α] [UpwardEnumerable α] [LawfulUpwardEnumerableLT α] :
--     LawfulOpenUpperBound α where
--   isSatisfied_iff_le u a := by simp [SupportsUpperBound.IsSatisfied, LawfulUpwardEnumerableLT.lt_iff]

-- instance {α} [UpwardEnumerable α] : LawfulUnboundedUpperBound α where
--   isSatisfied u a := by simp [SupportsUpperBound.IsSatisfied]

-- /--
-- This typeclass allows taking the intersection of ranges of the given shape and half-open ranges.

-- An element should be contained in the intersection if and only if it is contained in both ranges.
-- This is encoded in `LawfulClosedOpenIntersection`.
-- -/
-- class ClosedOpenIntersection (shape : RangeShape) (α : Type w) where
--   intersection : PRange shape α → PRange ⟨.closed, .open⟩ α → PRange ⟨.closed, .open⟩ α

-- /--
-- This typeclass ensures that the intersection according to `ClosedOpenIntersection shape α`
-- of two ranges contains exactly those elements that are contained in both ranges.
-- -/
-- class LawfulClosedOpenIntersection (shape : RangeShape) (α : Type w)
--     [ClosedOpenIntersection shape α]
--     [SupportsLowerBound shape.lower α] [SupportsUpperBound shape.upper α]
--     [SupportsLowerBound .closed α]
--     [SupportsUpperBound .open α] where
--   /--
--   The intersection according to `ClosedOpenIntersection shape α` of two ranges contains exactly
--   those elements that are contained in both ranges.
--   -/
--   mem_intersection_iff {a : α} {r : PRange ⟨shape.lower, shape.upper⟩ α}
--       {s : PRange ⟨.closed, .open⟩ α} :
--     a ∈ ClosedOpenIntersection.intersection r s ↔ a ∈ r ∧ a ∈ s

class Rcc.HasRcoIntersection (α : Type w) where
  intersection : Rcc α → Rco α → Rco α

class Rcc.LawfulRcoIntersection (α : Type w) [LT α] [LE α]
    [HasRcoIntersection α] where
  mem_intersection_iff {a : α} {r : Rcc α} {s : Rco α} :
    a ∈ HasRcoIntersection.intersection r s ↔ a ∈ r ∧ a ∈ s

class Rco.HasRcoIntersection (α : Type w) where
  intersection : Rco α → Rco α → Rco α

class Rco.LawfulRcoIntersection (α : Type w) [LT α] [LE α]
    [HasRcoIntersection α] where
  mem_intersection_iff {a : α} {r : Rco α} {s : Rco α} :
    a ∈ HasRcoIntersection.intersection r s ↔ a ∈ r ∧ a ∈ s

class Rci.HasRcoIntersection (α : Type w) where
  intersection : Rci α → Rco α → Rco α

class Rci.LawfulRcoIntersection (α : Type w) [LT α] [LE α]
    [HasRcoIntersection α] where
  mem_intersection_iff {a : α} {r : Rci α} {s : Rco α} :
    a ∈ HasRcoIntersection.intersection r s ↔ a ∈ r ∧ a ∈ s

class Roc.HasRcoIntersection (α : Type w) where
  intersection : Roc α → Rco α → Rco α

class Roc.LawfulRcoIntersection (α : Type w) [LT α] [LE α]
    [HasRcoIntersection α] where
  mem_intersection_iff {a : α} {r : Roc α} {s : Rco α} :
    a ∈ HasRcoIntersection.intersection r s ↔ a ∈ r ∧ a ∈ s

class Roo.HasRcoIntersection (α : Type w) where
  intersection : Roo α → Rco α → Rco α

class Roo.LawfulRcoIntersection (α : Type w) [LT α] [LE α]
    [HasRcoIntersection α] where
  mem_intersection_iff {a : α} {r : Roo α} {s : Rco α} :
    a ∈ HasRcoIntersection.intersection r s ↔ a ∈ r ∧ a ∈ s

class Roi.HasRcoIntersection (α : Type w) where
  intersection : Roi α → Rco α → Rco α

class Roi.LawfulRcoIntersection (α : Type w) [LT α] [LE α]
    [HasRcoIntersection α] where
  mem_intersection_iff {a : α} {r : Roi α} {s : Rco α} :
    a ∈ HasRcoIntersection.intersection r s ↔ a ∈ r ∧ a ∈ s

class Ric.HasRcoIntersection (α : Type w) where
  intersection : Ric α → Rco α → Rco α

class Ric.LawfulRcoIntersection (α : Type w) [LT α] [LE α]
    [HasRcoIntersection α] where
  mem_intersection_iff {a : α} {r : Ric α} {s : Rco α} :
    a ∈ HasRcoIntersection.intersection r s ↔ a ∈ r ∧ a ∈ s

class Rio.HasRcoIntersection (α : Type w) where
  intersection : Rio α → Rco α → Rco α

class Rio.LawfulRcoIntersection (α : Type w) [LT α] [LE α]
    [HasRcoIntersection α] where
  mem_intersection_iff {a : α} {r : Rio α} {s : Rco α} :
    a ∈ HasRcoIntersection.intersection r s ↔ a ∈ r ∧ a ∈ s

class Rii.HasRcoIntersection (α : Type w) where
  intersection : Rii α → Rco α → Rco α

class Rii.LawfulRcoIntersection (α : Type w) [LT α] [LE α]
    [HasRcoIntersection α] where
  mem_intersection_iff {a : α} {r : Rii α} {s : Rco α} :
    a ∈ HasRcoIntersection.intersection r s ↔ a ∈ r ∧ a ∈ s

end Std
