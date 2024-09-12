theorem ex1 (a : α) (b : List α) : (a::b = []) = False :=
  by simp

theorem ex2 (a : α) (b : List α) : (a::b = []) = False :=
  by simp

theorem ex3 (x : Nat) : (if Nat.succ x = 0 then 1 else 2) = 2 :=
  by simp

theorem ex4 (x : Nat) : (if 10 = 0 then 1 else 2) = 2 :=
  by simp

theorem ex5 : (10 = 20) = False :=
  by simp

/--
info: theorem ex5 : (10 = 20) = False :=
of_eq_true (Eq.trans (congrArg (fun x => x = False) (eq_false_of_decide (Eq.refl false))) (eq_self False))
-/
#guard_msgs in
#print ex5

theorem ex6 : (if "hello" = "world" then 1 else 2) = 2 :=
  by simp (config := { decide := true })

/--
info: theorem ex6 : (if "hello" = "world" then 1 else 2) = 2 :=
of_eq_true (eq_true_of_decide (Eq.refl true))
-/
#guard_msgs in
#print ex6

theorem ex7 : (if "hello" = "world" then 1 else 2) = 2 := by
  simp (config := { decide := false }) [-String.reduceEq]
  guard_target =ₛ ¬ "hello" = "world"
  fail_if_success simp [-String.reduceEq]
  simp (config := { decide := true }) [-String.reduceEq]

theorem ex8 : (10 + 2000 = 20) = False :=
  by simp

def fact : Nat → Nat
  | 0 => 1
  | x+1 => (x+1) * fact x

theorem ex9 : (if fact 100 > 10 then true else false) = true :=
  by simp (config := { decide := true })
