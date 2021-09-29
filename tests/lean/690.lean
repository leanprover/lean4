example (a b : Nat) (h : Nat.le a b) : Nat.le a (b + 1) := by
  induction h with
  | step x? hStep ih => admit
  | refl => admit

example (a b : Nat) (h : Nat.le a b) : Nat.le a (b + 1) := by
  induction h with
  | step hStep ih => trace_state; admit
  | refl => admit

example (a b : Nat) (h : Nat.le a b) : Nat.le a (b + 1) := by
  induction h with
  | @step x hStep ih => trace_state; admit
  | refl => admit
