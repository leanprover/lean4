def f (x : Nat) := x + 1

theorem f_eq (x : Nat) : f (x + 1) = x + 2 := rfl

theorem ex1 : f (f (x + 1)) = x + 3 := by
  simp -implicitDefEqProofs [f_eq]

/--
info: theorem ex1 : ∀ {x : Nat}, f (f (x + 1)) = x + 3 :=
fun {x} =>
  of_eq_true
    (Eq.trans (congrArg (fun x_1 => x_1 = x + 3) (Eq.trans (congrArg f (f_eq x)) (f_eq (x + 1)))) (eq_self (x + 1 + 2)))
-/
#guard_msgs in
#print ex1

theorem ex2 : f (f (x + 1)) = x + 3 := by
  simp +implicitDefEqProofs [f_eq]

/--
info: theorem ex2 : ∀ {x : Nat}, f (f (x + 1)) = x + 3 :=
fun {x} => of_eq_true (eq_self (x + 1 + 2))
-/
#guard_msgs in
#print ex2
