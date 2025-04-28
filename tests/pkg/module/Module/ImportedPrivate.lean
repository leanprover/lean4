module

prelude
private import private Module.Basic

/-! `import private` should uncover theorem bodies. -/

/--
info: theorem t : f = 1 :=
sorry
-/
#guard_msgs in
#print t
