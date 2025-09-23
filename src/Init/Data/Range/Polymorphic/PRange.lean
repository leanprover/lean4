/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Core
public import Init.Data.Range.Polymorphic.UpwardEnumerable

set_option doc.verso true

public section

namespace Std

open PRange

/--
A range of elements of {given}`α` with closed lower and upper bounds.

{lit}`a...=b` is the range of all values greater than or equal to {given}`a : α` and less than or
equal to {given}`b : α`. This is notation for {lean}`Rcc.mk a b`.
-/
structure Rcc (α : Type u) where
  lower : α
  upper : α

/--
A range of elements of {given}`α` with a closed lower bound and an open upper bound.

{lit}`a...b` or {lit}`a...<b` is the range of all values greater than or equal to {given}`a : α` and
less than {given}`b : α`. This is notation for {lean}`Rco.mk a b`.
-/
structure Rco (α : Type u) where
  lower : α
  upper : α

/--
An upward-unbounded range of elements of {given}`α` with a closed lower bound.

{lit}`a...*` is the range of all values greater than or equal to {given}`a : α`.
This is notation for {lean}`Rci.mk a`.
-/
structure Rci (α : Type u) where
  lower : α

/--
A range of elements of {given}`α` with an open lower bound and a closed upper bound.

{lit}`a<...=b` is the range of all values greater than {given}`a : α` and less than or equal to
{given}`b : α`. This is notation for {lean}`Roc.mk a b`.
-/
structure Roc (α : Type u) where
  lower : α
  upper : α

/--
A range of elements of {given}`α` with an open lower and upper bounds.

{lit}`a<...b` or {lit}`a<...<b` is the range of all values greater than {given}`a : α` and less than
{given}`b : α`. This is notation for {lean}`Roo.mk a b`.
-/
structure Roo (α : Type u) where
  lower : α
  upper : α

/--
An upward-unbounded range of elements of {given}`α` with an open lower bound.

{lit}`a<...*` is the range of all values greater than {given}`a : α`.
This is notation for {lean}`Roi.mk a`.
-/
structure Roi (α : Type u) where
  lower : α

/--
A downward-unbounded range of elements of {given}`α` with a closed upper bound.

{lit}`*...=b` is the range of all values less than or equal to {given}`b : α`.
This is notation for {lean}`Ric.mk b`.
-/
structure Ric (α : Type u) where
  upper : α

/--
A downward-unbounded range of elements of {given}`α` with an open upper bound.

{lit}`*...b` or {lit}`*...<b` is the range of all values less than {given}`b : α`.
This is notation for {lean}`Rio.mk b`.
-/
structure Rio (α : Type u) where
  upper : α

/--
A full range of all elements of {lit}`α`. Its only inhabitant is the range {lit}`*...*`, which is
notation for {lean}`Rii.mk`.
-/
structure Rii (α : Type u) where

/-- `a...*` is the range of elements greater than or equal to {lit}`a`. See also {name}`Std.Rci`. -/
syntax:max (term "...*") : term
/-- `*...*` is the range that is unbounded in both directions. See also {lean}`Std.Rii`. -/
syntax:max ("*...*") : term
/-- `a<...*` is the range of elements greater than {lit}`a`. See also {lean}`Std.Roi`. -/
syntax:max (term "<...*") : term
/--
`a...<b` is the range of elements greater than or equal to {lit}`a` and less than {lit}`b`.
See also {lean}`Std.Rco`.
-/
syntax:max (term "...<" term) : term
/--
`a...b` is the range of elements greater than or equal to {lit}`a` and less than {lit}`b`.
See also {lean}`Std.Rco`.
-/
syntax:max (term "..." term) : term
/-- `*...<b` is the range of elements less than {lit}`b`. See also {lean}`Std.Rio`. -/
syntax:max ("*...<" term) : term
/-- `*...b` is the range of elements less than {lit}`b`. See also {lean}`Std.Rio`. -/
syntax:max ("*..." term) : term
/--
`a<...<b` is the range of elements greater than {lit}`a` and less than {lit}`b`.
See also {lean}`Std.Roo`.
-/
syntax:max (term "<...<" term) : term
/--
`a<...b` is the range of elements greater than {lit}`a` and less than {lit}`b`.
See also {lean}`Std.Roo`.
-/
syntax:max (term "<..." term) : term
/--
`a...=b` is the range of elements greater than or equal to {lit}`a` and less than or equal to
{lit}`b`. See also {lean}`Std.Rcc`.
-/
syntax:max (term "...=" term) : term
/-- `*...=b` is the range of elements less than or equal to {lit}`b`. See also {lean}`Std.Ric`. -/
syntax:max ("*...=" term) : term
/--
`a<...=b` is the range of elements greater than {lit}`a` and less than or equal to {lit}`b`.
See also {lean}`Std.Roc`.
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
This type class ensures that right-closed ranges (i.e., for bounds {given}`a` and {given}`b`,
{lean}`a...=b`, {lean}`a<...=b` and {lean}`*...=b`) are always finite.
This is a prerequisite for many functions and instances, such as
{name (scope := "Init.Data.Range.Polymorphic.Iterators")}`Rcc.toList` or {name}`ForIn'`.
-/
class Rxc.IsAlwaysFinite (α : Type u) [UpwardEnumerable α] [LE α] : Prop where
  finite (init : α) (hi : α) :
    ∃ n, (UpwardEnumerable.succMany? n init).elim True (¬ · ≤ hi)

/--
This type class ensures that right-open ranges (i.e., for bounds {given}`a` and {given}`b`,
{lean}`a...b`, {lean}`a<...b` and {lean}`*...b`) are always finite.
This is a prerequisite for many functions and instances, such as
{name (scope := "Init.Data.Range.Polymorphic.Iterators")}`Rco.toList` or {name}`ForIn'`.
-/
class Rxo.IsAlwaysFinite (α : Type u) [UpwardEnumerable α] [LT α] : Prop where
  finite (init : α) (hi : α) :
    ∃ n, (UpwardEnumerable.succMany? n init).elim True (¬ · < hi)

/--
This type class ensures that right-unbounded ranges (i.e., for a bound {given}`a`,
{lean}`a...*`, {lean}`a<...*` and {lean}`*...*`) are always finite.
This is a prerequisite for many functions and instances, such as
{name (scope := "Init.Data.Range.Polymorphic.Iterators")}`Rci.toList` or {name}`ForIn'`.
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

/--
This type class allows taking the intersection of a closed range with a
left-closed right-open range, resulting in another left-closed right-open range.
-/
class Rcc.HasRcoIntersection (α : Type w) where
  intersection : Rcc α → Rco α → Rco α

/--
This type class ensures that the intersection according to {name}`Rcc.HasRcoIntersection`
of two ranges contains exactly those elements that are contained in both ranges.
-/
class Rcc.LawfulRcoIntersection (α : Type w) [LT α] [LE α]
    [HasRcoIntersection α] where
  mem_intersection_iff {a : α} {r : Rcc α} {s : Rco α} :
    a ∈ HasRcoIntersection.intersection r s ↔ a ∈ r ∧ a ∈ s

/--
This type class allows taking the intersection of two left-closed right-open ranges, resulting in
another left-closed right-open range.
-/
class Rco.HasRcoIntersection (α : Type w) where
  intersection : Rco α → Rco α → Rco α

/--
This type class ensures that the intersection according to {name}`Rco.HasRcoIntersection`
of two ranges contains exactly those elements that are contained in both ranges.
-/
class Rco.LawfulRcoIntersection (α : Type w) [LT α] [LE α]
    [HasRcoIntersection α] where
  mem_intersection_iff {a : α} {r : Rco α} {s : Rco α} :
    a ∈ HasRcoIntersection.intersection r s ↔ a ∈ r ∧ a ∈ s

/--
This type class allows taking the intersection of a left-closed right-unbounded range with a
left-closed right-open range, resulting in another left-closed right-open range.
-/
class Rci.HasRcoIntersection (α : Type w) where
  intersection : Rci α → Rco α → Rco α

/--
This type class ensures that the intersection according to {name}`Rci.HasRcoIntersection`
of two ranges contains exactly those elements that are contained in both ranges.
-/
class Rci.LawfulRcoIntersection (α : Type w) [LT α] [LE α]
    [HasRcoIntersection α] where
  mem_intersection_iff {a : α} {r : Rci α} {s : Rco α} :
    a ∈ HasRcoIntersection.intersection r s ↔ a ∈ r ∧ a ∈ s

/--
This type class allows taking the intersection of a left-open right-closed range with a
left-closed right-open range, resulting in another left-closed right-open range.
-/
class Roc.HasRcoIntersection (α : Type w) where
  intersection : Roc α → Rco α → Rco α

/--
This type class ensures that the intersection according to {name}`Roc.HasRcoIntersection`
of two ranges contains exactly those elements that are contained in both ranges.
-/
class Roc.LawfulRcoIntersection (α : Type w) [LT α] [LE α]
    [HasRcoIntersection α] where
  mem_intersection_iff {a : α} {r : Roc α} {s : Rco α} :
    a ∈ HasRcoIntersection.intersection r s ↔ a ∈ r ∧ a ∈ s

/--
This type class allows taking the intersection of an open range with a
left-closed right-open range, resulting in another left-closed right-open range.
-/
class Roo.HasRcoIntersection (α : Type w) where
  intersection : Roo α → Rco α → Rco α

/--
This type class ensures that the intersection according to {name}`Roo.HasRcoIntersection`
of two ranges contains exactly those elements that are contained in both ranges.
-/
class Roo.LawfulRcoIntersection (α : Type w) [LT α] [LE α]
    [HasRcoIntersection α] where
  mem_intersection_iff {a : α} {r : Roo α} {s : Rco α} :
    a ∈ HasRcoIntersection.intersection r s ↔ a ∈ r ∧ a ∈ s

/--
This type class allows taking the intersection of a left-open right-unbounded range with a
left-closed right-open range, resulting in another left-closed right-open range.
-/
class Roi.HasRcoIntersection (α : Type w) where
  intersection : Roi α → Rco α → Rco α

/--
This type class ensures that the intersection according to {name}`Roi.HasRcoIntersection`
of two ranges contains exactly those elements that are contained in both ranges.
-/
class Roi.LawfulRcoIntersection (α : Type w) [LT α] [LE α]
    [HasRcoIntersection α] where
  mem_intersection_iff {a : α} {r : Roi α} {s : Rco α} :
    a ∈ HasRcoIntersection.intersection r s ↔ a ∈ r ∧ a ∈ s

/--
This type class allows taking the intersection of a left-unbounded right-closed range with a
left-closed right-open range, resulting in another left-closed right-open range.
-/
class Ric.HasRcoIntersection (α : Type w) where
  intersection : Ric α → Rco α → Rco α

/--
This type class ensures that the intersection according to {name}`Ric.HasRcoIntersection`
of two ranges contains exactly those elements that are contained in both ranges.
-/
class Ric.LawfulRcoIntersection (α : Type w) [LT α] [LE α]
    [HasRcoIntersection α] where
  mem_intersection_iff {a : α} {r : Ric α} {s : Rco α} :
    a ∈ HasRcoIntersection.intersection r s ↔ a ∈ r ∧ a ∈ s

/--
This type class allows taking the intersection of a left-unbounded right-open range with a
left-closed right-open range, resulting in another left-closed right-open range.
-/
class Rio.HasRcoIntersection (α : Type w) where
  intersection : Rio α → Rco α → Rco α

/--
This type class ensures that the intersection according to {name}`Rio.HasRcoIntersection`
of two ranges contains exactly those elements that are contained in both ranges.
-/
class Rio.LawfulRcoIntersection (α : Type w) [LT α] [LE α]
    [HasRcoIntersection α] where
  mem_intersection_iff {a : α} {r : Rio α} {s : Rco α} :
    a ∈ HasRcoIntersection.intersection r s ↔ a ∈ r ∧ a ∈ s

end Std
