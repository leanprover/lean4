/--
error: Invalid dotted identifier notation: Not supported on type universe
  Prop
-/
#guard_msgs in
def foo (n : Nat) : Nat :=
  match n < 42 with
  | .true => n
  | .false => 47

set_option pp.mvars.anonymous false in
/--
error: Invalid dotted identifier notation: Not supported on type universe
  Sort _
-/
#guard_msgs in
def foo2 (n : Nat) : Nat :=
  match PUnit with
  | .unit => n

def Prop.true := True

/--
error: Invalid dotted identifier notation: Not supported on type universe
  Prop
-/
#guard_msgs in
#check (.true : Prop)
