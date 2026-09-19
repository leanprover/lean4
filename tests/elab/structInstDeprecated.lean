module

/-!
Regression tests for #15203: explicitly written deprecated structure fields warn in
structure instances, while implicitly supplied fields and suppressed contexts do not.
-/

set_option linter.deprecated true

structure Point where
  x : Nat
  y : Nat := 0

structure LabeledPoint extends Point where
  label : Nat

structure PointPair where
  fst : Point
  snd : Point

attribute [deprecated Point.x (since := "2026-01-01")] Point.y

-- Warn on explicit assignments, without suggesting an invalid field-name replacement.
/-- warning: `Point.y` has been deprecated: Use `Point.x` instead -/
#guard_msgs in
open Point (y) in
example : Point := { x := 1, y := 2 }

/-- warning: `Point.y` has been deprecated: Use `Point.x` instead -/
#guard_msgs in
example : LabeledPoint := { x := 1, y := 2, label := 3 }

attribute [deprecated PointPair.fst (since := "2026-01-01")] PointPair.snd

-- Each written component gets exactly one warning at its original source location.
/--
@ +3:4...7
warning: `PointPair.snd` has been deprecated: Use `PointPair.fst` instead
---
@ +4:4...7
warning: `PointPair.snd` has been deprecated: Use `PointPair.fst` instead
---
@ +4:8...9
warning: `Point.y` has been deprecated: Use `Point.x` instead
-/
#guard_msgs (positions := true, ordering := sorted) in
example : PointPair :=
  { fst := { x := 0 }
    snd.x := 1
    snd.y := 2 }

-- Generated projections must neither duplicate field warnings nor suppress the user's RHS.
/--
warning: `Point.y` has been deprecated: Use `Point.x` instead
---
warning: `PointPair.snd` has been deprecated: Use `PointPair.fst` instead
-/
#guard_msgs (ordering := sorted) in
example (p : PointPair) (q : Point) : PointPair := { p with snd.x := q.y }

-- Omitted defaults and fields copied from sources do not constitute explicit uses.
#guard_msgs in
example : Point := { x := 1 }

#guard_msgs in
example (p : Point) : Point := { p with x := 1 }

-- Both suppression mechanisms propagate through synthetic nested structure instances.
#guard_msgs in
set_option linter.deprecated false in
example (p : PointPair) : PointPair := { p with snd.y := 2 }

#guard_msgs in
@[deprecated "Use another pair" (since := "2026-01-01")]
def deprecatedPair (p : PointPair) : PointPair := { p with snd.y := 2 }

class HasValue where
  value : Nat

attribute [deprecated "Use another class" (since := "2026-09-19")] HasValue.value

-- Class instances and `where` notation use the same field checks.
/-- warning: `HasValue.value` has been deprecated: Use another class -/
#guard_msgs in
instance : HasValue where
  value := 1

@[deprecated "Use another source" (since := "2026-09-19")]
def oldPairSource : PointPair := { fst := { x := 0 }, snd := { x := 0 } }

-- Warnings on the original source expression must survive generated-projection suppression.
/-- warning: `oldPairSource` has been deprecated: Use another source -/
#guard_msgs in
example : PointPair := { oldPairSource with fst.x := 1 }

namespace ParentSelection

-- Two fields ensure a parent assignment warns once, not once per expanded field.
structure Root where
  value : Nat
  other : Nat := 0

structure Mid extends Root where
  extra : Nat

structure Leaf extends Mid, Root where
  flag : Bool

structure Descendant extends Leaf

structure OtherLeaf extends Mid, Root where
  flag : Bool

attribute [deprecated "Set the fields directly" (since := "2026-09-19")] Leaf.toRoot

-- Check the named direct projection, not the subobject path through Mid.
/-- warning: `ParentSelection.Leaf.toRoot` has been deprecated: Set the fields directly -/
#guard_msgs in
example (r : Root) : Leaf := { toRoot := r, extra := 0, flag := false }

-- Parent prefixes must be checked before normalization consumes them.
/--
@ +2:4...10
warning: `ParentSelection.Leaf.toRoot` has been deprecated: Set the fields directly
-/
#guard_msgs (positions := true) in
example : Leaf :=
  { toRoot.value := 1, extra := 0, flag := false }

-- Inherited names must resolve to the original projection declaration.
/-- warning: `ParentSelection.Leaf.toRoot` has been deprecated: Set the fields directly -/
#guard_msgs in
example : Descendant := { toRoot.value := 1, extra := 0, flag := false }

-- An implicit parent projection is not an explicit use.
#guard_msgs in
example : Leaf := { value := 1, extra := 0, flag := false }

-- Parent checks respect the same two suppression mechanisms as ordinary fields.
#guard_msgs in
set_option linter.deprecated false in
example : Leaf := { toRoot.value := 1, extra := 0, flag := false }

#guard_msgs in
@[deprecated "Use another leaf" (since := "2026-09-19")]
def deprecatedLeaf : Leaf := { toRoot.value := 1, extra := 0, flag := false }

attribute [deprecated "Set Mid fields directly" (since := "2026-09-19")] Mid.toRoot

-- An unwritten deprecated path must not warn; explicitly selecting it must warn.
#guard_msgs in
example (r : Root) : OtherLeaf := { toRoot := r, extra := 0, flag := false }

/-- warning: `ParentSelection.Mid.toRoot` has been deprecated: Set Mid fields directly -/
#guard_msgs in
example : OtherLeaf := { toMid.toRoot.value := 1, extra := 0, flag := false }

end ParentSelection
