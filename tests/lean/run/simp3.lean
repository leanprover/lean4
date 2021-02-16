constant f (x : Nat) : Nat
@[simp] axiom fEq (x : Nat) : f x = x

theorem ex1 (x : Nat) : f (f x, x).fst = x := by simp

theorem ex2 (x : Nat) : f ((fun a => f (f a)) x) = x := by simp

constant g (x : Nat) : Nat
@[simp] axiom gEq (x : Nat) : g x = match x with | 0 => 1 | x+1 => 2
@[simp] theorem add1 (x : Nat) : x + 1 = x.succ := rfl

theorem ex3 (x : Nat) : g (x + 1) = 2 := by simp

theorem ex4 (x : Nat) : (fun x => x + 1) = (fun x => x.succ) := by simp

@[simp] theorem comm (x y : Nat) : x + y = y + x := Nat.add_comm ..

theorem ex5 (x y : Nat) : (fun x y : Nat => x + 0 + y) = (fun x y : Nat => y + x + 0) := by simp
