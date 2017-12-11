open tactic

example : true :=
by do
  let n := 10,
  let b := 20,
  trace $ n + b,
  constructor

example : true ∧ true :=
by do
  t ← target,
  let f := t^.get_app_fn,
  trace f,
  constructor,
  repeat triv

example : true ∧ true :=
by do
  t ← target,
  let f := t^.get_app_fn in
  constructor >> skip; triv
