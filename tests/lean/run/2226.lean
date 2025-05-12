/--
error: unsolved goals
A : Nat
⊢ Sort ?u.3
-/
#guard_msgs in
variable (A : Nat) (B : by skip)

/--
error: Failed to infer definition type.

context:
A : Nat
B : sorry
⊢ Sort ?u.13
-/
#guard_msgs in
def foo :=
  A = B

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
def boo :=
  B
