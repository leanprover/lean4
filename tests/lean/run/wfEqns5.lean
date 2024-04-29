
def foo : Nat → Nat → Nat
  | 0, m => match m with | 0 => 0 | m => m
  | n+1, m => foo n m
termination_by n => n

/--
info: foo.eq_1 :
  ∀ (x : Nat),
    foo 0 x =
      match x with
      | 0 => 0
      | m => m
-/
#guard_msgs in
#check foo.eq_1

/-- info: foo.eq_2 : ∀ (x n : Nat), foo n.succ x = foo n x -/
#guard_msgs in
#check foo.eq_2

/--
info: foo.eq_def :
  ∀ (x x_1 : Nat),
    foo x x_1 =
      match x, x_1 with
      | 0, m =>
        match m with
        | 0 => 0
        | m => m
      | n.succ, m => foo n m
-/
#guard_msgs in
#check foo.eq_def

/-- error: unknown identifier 'foo.eq_3' -/
#guard_msgs in
#check foo.eq_3
