module

prelude
public import Module.PrivateImported
import all Module.PrivateImported

/-! `import all` should activate nested `private import`s. -/

/-- info: f : Nat -/
#guard_msgs in
#check f
