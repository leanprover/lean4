/--
error: unsolved goals
A : Nat
⊢ Sort ?u.3
-/
#guard_msgs in
variable (A : Nat) (B : by skip)

/-- error: failed to infer type of `foo` -/
#guard_msgs in
def foo :=
  A = B

/--
warning: declaration uses 'sorry' due to elaboration errors.

This can be caused by (1) referring to declarations with elaboration errors or (2) bugs in elaborators. In the second case, please report a minimized error-free example that produces this warning.
-/
#guard_msgs in
def boo :=
  B
