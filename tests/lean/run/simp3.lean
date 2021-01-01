constant f (x : Nat) : Nat
@[simp] axiom fEq (x : Nat) : f x = x

theorem ex1 (x : Nat) : f (f x, x).fst = x := by simp

theorem ex2 (x : Nat) : f ((fun a => f (f a)) x) = x := by simp

constant g (x : Nat) : Nat
@[simp] axiom gEq (x : Nat) : g x = match x with | 0 => 1 | x+1 => 2
@[simp] theorem add1 (x : Nat) : x + 1 = x.succ := rfl

theorem ex3 (x : Nat) : g (x + 1) = 2 := by simp
