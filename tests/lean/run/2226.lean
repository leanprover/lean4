/--
error: unsolved goals
A : Nat
⊢ Sort ?u.3
-/
#guard_msgs in
variable (A : Nat) (B : by skip)

def foo :=
  A = B

def boo :=
  B
