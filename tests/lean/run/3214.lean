set_option pp.mvars false

class Foo (α : Type)

/--
error: Function expected at
  Missing
but this term has type
  ?_

Note: Expected a function because this term is being applied to the argument
  α
-/
#guard_msgs in
variable {α : Type} (s : Missing α)

#synth Foo s
