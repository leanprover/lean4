/--
error: unsolved goals
A : Nat
⊢ Sort ?u.2
-/
#guard_msgs in
variable (A : Nat) (B : by skip)

/-- error: Failed to infer type of definition `foo` -/
#guard_msgs in
def foo :=
  A = B

/-- warning: declaration uses `sorry` -/
#guard_msgs in
def boo :=
  B
