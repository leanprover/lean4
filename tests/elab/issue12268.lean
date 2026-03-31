theorem foo : True := by
  let rec f (n : Nat) : Nat :=
    match n with
    | .zero => 0
    | .succ n => f n
  termination_by structural n
  trivial

theorem bar : True := by
  let rec f (n : Nat) : Nat :=
    match n with
    | .zero => 0
    | .succ n => f n
  termination_by n
  trivial
