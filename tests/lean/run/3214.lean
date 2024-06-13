class Foo (α : Type)

/--
error: function expected at
  Missing
term has type
  ?m.9
-/
#guard_msgs in
variable {α : Type} (s : Missing α)

#synth Foo s
