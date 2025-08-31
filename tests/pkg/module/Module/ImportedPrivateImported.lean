module

prelude
public import Module.PrivateImported

/-! `private import` should not be transitive. -/

/-- error: Unknown identifier `f` -/
#guard_msgs in
#check f
