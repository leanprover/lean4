module

prelude
public import Module.PrivateImported

/-! `private import` should not be transitive. -/

/-- error: Unknown identifier `f` -/
#guard_msgs in
#check f

/-- info: 5 -/
#guard_msgs in
#eval publicDefOfPrivatelyInitialized

/-! #12833: namespaces privately imported but publicly used must be re-exported. -/
open Namespaced
