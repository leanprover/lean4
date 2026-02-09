def f {α} (a b : α) := a

theorem f_Eq {α} (a b : α) : f a b = a :=
  rfl

theorem ex1 (a b c : α) : f (f a b) c = a := by
  simp -implicitDefEqProofs [f_Eq]

/--
info: theorem ex1.{u_1} : ∀ {α : Sort u_1} (a b c : α), f (f a b) c = a :=
fun {α} a b c =>
  of_eq_true
    (Eq.trans (congrFun' (congrArg Eq (Eq.trans (congrFun' (congrArg f (f_Eq a b)) c) (f_Eq a c))) a) (eq_self a))
-/
#guard_msgs in
#print ex1

theorem ex1' (a b c : α) : f (f a b) c = a := by
  simp +implicitDefEqProofs [f_Eq]

/--
info: theorem ex1'.{u_1} : ∀ {α : Sort u_1} (a b c : α), f (f a b) c = a :=
fun {α} a b c => of_eq_true (eq_self a)
-/
#guard_msgs in
#print ex1'

theorem ex2 (p : Nat → Bool) (x : Nat) (h : p x = true) : (if p x then 1 else 2) = 1 := by
  simp [h]

/--
info: theorem ex2 : ∀ (p : Nat → Bool) (x : Nat), p x = true → (if p x = true then 1 else 2) = 1 :=
fun p x h =>
  of_eq_true
    (Eq.trans
      (congrFun' (congrArg Eq (ite_cond_eq_true 1 2 (Eq.trans (congrFun' (congrArg Eq h) true) (eq_self true)))) 1)
      (eq_self 1))
-/
#guard_msgs in
#print ex2
