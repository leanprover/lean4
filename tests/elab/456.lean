set_option pp.mvars false

/--
error: failed to solve universe constraint
  u =?= max 1 _
while trying to unify
  Sort u : Type u
with
  Type : Type 1
-/
#guard_msgs in
def A : Sort u := { s : Prop // _ }
