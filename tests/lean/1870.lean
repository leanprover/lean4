structure T := (x y : nat)
example : T := by refine { x := 1, y := _}
example : T := by refine { x := 1, ..}
example : T := { x := 1, ..}
