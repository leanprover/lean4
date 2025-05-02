module

prelude
private import all Module.Basic

/-! `import all` should uncover theorem bodies. -/

/--
info: theorem t : f = 1 :=
sorry
-/
#guard_msgs in
#print t
