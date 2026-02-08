@[simp] def iota : Nat → List Nat
  | 0       => []
  | m@(n+1) => m :: iota n

/-- info: iota.eq_1 : iota 0 = [] -/
#guard_msgs in
#check iota.eq_1

/-- info: iota.eq_2 (n : Nat) : iota n.succ = n.succ :: iota n -/
#guard_msgs in
#check iota.eq_2

@[simp] def f : List Nat → List Nat × List Nat
 | xs@(x :: ys@(y :: [])) => (xs, ys)
 | xs@(x :: ys@(y :: zs)) => f zs
 | _ => ([], [])

/-- info: f.eq_1 (x_1 y : Nat) : f [x_1, y] = ([x_1, y], [y]) -/
#guard_msgs in
#check f.eq_1

/--
info: f.eq_2 (x_1 y : Nat) (zs : List Nat) (x_2 : zs = [] → False) : f (x_1 :: y :: zs) = f zs
-/
#guard_msgs in
#check f.eq_2

/--
info: f.eq_3 (x✝ : List Nat) (x_2 : ∀ (x y : Nat), x✝ = [x, y] → False)
  (x_3 : ∀ (x y : Nat) (zs : List Nat), x✝ = x :: y :: zs → False) : f x✝ = ([], [])
-/
#guard_msgs in
#check f.eq_3
