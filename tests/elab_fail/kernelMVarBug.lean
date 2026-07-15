-- This example used to produce
-- `error: (kernel) declaration has metavariables`
-- Because we were not registering postponed instance metavariables
def f {α : Type u} (a : α) : α :=
  let g a b := a + b
  g a a
