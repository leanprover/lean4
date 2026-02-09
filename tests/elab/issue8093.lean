axiom testSorry : α

def foo (n : Nat) (p : Nat) : Nat :=
  foo (foo (n - 1) p) p
termination_by n
decreasing_by all_goals exact testSorry

/--
info: foo.induct (p : Nat) (motive : Nat → Prop) (case1 : ∀ (x : Nat), motive (x - 1) → motive (foo (x - 1) p) → motive x)
  (n : Nat) : motive n
-/
#guard_msgs in
#check foo.induct
