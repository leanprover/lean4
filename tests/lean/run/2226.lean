/--
error: unsolved goals
A : Nat
⊢ Sort ?u.3
-/
#guard_msgs in
variable (A : Nat) (B : by skip)

/--
error: type mismatch
  B
has type
  sorry : Sort ?u.9
but is expected to have type
  Nat : Type
-/
#guard_msgs in
def foo :=
  A = B

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
def boo :=
  B
