/-!
# Reduce parents in structure `extends` clause
-/

structure A
abbrev B := A

/-!
This already worked before the fix. Structure instances unfold the expected type.
-/
/-- info: { } : A -/
#guard_msgs in #check { : B}

/-!
This is now allowed. The parent `B` is unfolded.
-/
structure C extends B

/-- info: { } : C -/
#guard_msgs in #check { : C}

/-!
Note that the parent projection is for `A`, not `B`.
-/
/-- info: C.toA (self : C) : A -/
#guard_msgs in #check C.toA
