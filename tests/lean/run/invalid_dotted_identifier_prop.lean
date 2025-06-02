/--
error: Invalid dotted identifier notation: not supported on type
  Prop
-/
#guard_msgs in
def foo (n : Nat) : Nat :=
  match n < 42 with
  | .true => n
  | .false => 47

/--
error: Invalid dotted identifier notation: not supported on type
  Sort ?u.44
-/
#guard_msgs in
def foo2 (n : Nat) : Nat :=
  match PUnit with
  | .unit => n

def Prop.true := True

/--
error: Invalid dotted identifier notation: not supported on type
  Prop
-/
#guard_msgs in
#check (.true : Prop)
