opaque g (x y : Nat) : Nat
opaque f (x y : Nat) : Nat
axiom f_def (x y : Nat) : f x y = g x y
axiom f_ax (x : Nat) : f x x = x

theorem ex1 (x : Nat) : g x x = x := by
  simp [← f_def, f_ax]

opaque P (x y : Nat) : Prop
opaque Q (x y : Nat) : Prop
axiom p_def (x y : Nat) : P x y ↔ Q x y
axiom p_ax (x : Nat) : P x x

theorem ex2 (x : Nat) : Q x x := by
  simp [← p_def, p_ax]
