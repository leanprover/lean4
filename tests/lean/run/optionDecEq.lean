variable {α : Type u} [DecidableEq α]

-- test for instance diamonds

example (x : Option α) :
    Option.instDecidableEq x none = Option.decidableEqNone x := by
  with_reducible_and_instances rfl

example (x : Option α) :
    Option.instDecidableEq none x = Option.decidableNoneEq x := by
  with_reducible_and_instances rfl
