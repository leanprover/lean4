/-- error: `f.go` has already been declared -/
#guard_msgs in
def f (x : Nat) : Nat :=
  go x
where
  go (x : Nat) : Nat := x
  go (x : Nat) : Nat := x + 1

/-- error: `g.go` has already been declared -/
#guard_msgs in
def g (x : Nat) : Nat :=
  go x
where
  go (x : Nat) : Nat := x
  go (x : Nat) (y : Nat) : Nat := x + 1
