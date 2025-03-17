/--
error: unsolved goals
A : Nat
⊢ Sort ?u.3
-/
#guard_msgs in
variable (A : Nat) (B : by skip)

/-- error: failed to infer definition type -/
#guard_msgs in
def foo :=
  A = B

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
def boo :=
  B
