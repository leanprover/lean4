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

#check foo._unfold
