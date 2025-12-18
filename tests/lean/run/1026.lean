def foo (n : Nat) : Nat :=
  if n = 0 then 0 else
    let x := n - 1
    have := match () with | _ => trivial
    foo x
termination_by n
decreasing_by sorry

theorem ex : foo 0 = 0 := by
  unfold foo
  sorry

/--
info: foo.eq_def (n : Nat) :
  foo n =
    if n = 0 then 0
    else
      have x := n - 1;
      have this := foo._proof_3;
      foo x
-/
#guard_msgs in
#check foo.eq_def

/--
info: foo.eq_unfold :
  foo = fun n =>
    if n = 0 then 0
    else
      have x := n - 1;
      have this := foo._proof_3;
      foo x
-/
#guard_msgs in
#check foo.eq_unfold
