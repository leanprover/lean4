constant g (x y : Nat) : Nat
constant f (x y : Nat) : Nat
axiom f_def (x y : Nat) : f x y = g x y
axiom f_ax (x : Nat) : f x x = x

theorem ex1 (x : Nat) : g x x = x := by
  simp [← f_def, f_ax]

constant p (x y : Nat) : Prop
constant q (x y : Nat) : Prop
axiom p_def (x y : Nat) : p x y ↔ q x y
axiom p_ax (x : Nat) : p x x

theorem ex2 (x : Nat) : q x x := by
  simp [← p_def, p_ax]
