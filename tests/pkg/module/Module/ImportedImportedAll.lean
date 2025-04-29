module

prelude
import Module.ImportedAll

/-! `import all` should not transitively expose private info. -/

/--
info: def f : Nat :=
1
-/
#guard_msgs in
#print f
