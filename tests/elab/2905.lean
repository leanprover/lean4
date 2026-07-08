import Lean
/-!
# Only direct parents of classes are instances

https://github.com/leanprover/lean4/issues/2905
-/

set_option structure.strictResolutionOrder true

class A
class B
class C extends A
class D extends A, B
class E extends C, D

/-!
These were or were not instances before #5902 and still are or are not.
-/
/-- info: some 1000 -/
#guard_msgs in #eval return (←Lean.Meta.getInstancePriority? `E.toC)
/-- info: some 1000 -/
#guard_msgs in #eval return (←Lean.Meta.getInstancePriority? `E.toD)
/-- info: none -/
#guard_msgs in #eval return (←Lean.Meta.getInstancePriority? `E.toA)

/-!
This was an instance before #5902 and no longer is.
-/
/-- info: none -/
#guard_msgs in #eval return (←Lean.Meta.getInstancePriority? `E.toB)


/-!
Check that `A` is not an instance, since it is implied by the others.
-/
class E' extends C, D, A

/-- info: none -/
#guard_msgs in #eval return (←Lean.Meta.getInstancePriority? `E'.toA_1)
/-- info: none -/
#guard_msgs in #eval return (←Lean.Meta.getInstancePriority? `E'.toB)
/-- info: some 1000 -/
#guard_msgs in #eval return (←Lean.Meta.getInstancePriority? `E'.toC)
/-- info: some 1000 -/
#guard_msgs in #eval return (←Lean.Meta.getInstancePriority? `E'.toD)
