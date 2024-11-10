import Lean
/-!
# Only direct parents of classes are instances

https://github.com/leanprover/lean4/issues/2905
-/

class A
class B
class C extends A
class D extends A, B
class E extends C, D

/-!
These were instances before #5902 and still are.
-/
/-- info: true -/
#guard_msgs in #eval return (←Lean.Meta.getInstancePriority? `E.toC) == some 1000
/-- info: true -/
#guard_msgs in #eval return (←Lean.Meta.getInstancePriority? `E.toD) == some 1000
/-- info: true -/
#guard_msgs in #eval return (←Lean.Meta.getInstancePriority? `E.toA) == none

/-!
This was an instance before #5902 and no longer is.
-/
/-- info: false -/
#guard_msgs in #eval return (←Lean.Meta.getInstancePriority? `E.toB) == some 1000
