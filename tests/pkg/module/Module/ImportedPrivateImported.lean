module

prelude
import Module.PrivateImported

/-! `private import` should not be transitive. -/

/-- error: unknown identifier 'f' -/
#guard_msgs in
#check f
