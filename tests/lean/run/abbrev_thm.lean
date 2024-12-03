theorem foo : True := by trivial
abbrev foo' := foo

/--
info: theorem foo' : True :=
foo
-/
#guard_msgs in
#print foo'
