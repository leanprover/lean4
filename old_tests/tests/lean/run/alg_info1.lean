open tactic

example : true :=
by do
  let op : expr := `((+) : nat → nat → nat),
  trace op,
  trace_algebra_info op,
  constructor
