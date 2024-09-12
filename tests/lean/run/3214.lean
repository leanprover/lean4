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

#synth Foo s
