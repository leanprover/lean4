set_option pp.mvars false

class Foo (α : Type)

/--
error: function expected at
  Missing
term has type
  ?_
-/
#guard_msgs in
variable {α : Type} (s : Missing α)

/--
error: application type mismatch
  Foo s
argument
  s
has type
  sorry : Sort _
but is expected to have type
  Type : Type 1
-/
#guard_msgs in
#synth Foo s
