module

prelude
public import Module.ImportedAll

/-! `import all` should not transitively expose private info. -/

/--
info: def f : Nat :=
<not imported>
-/
#guard_msgs in
#print f
