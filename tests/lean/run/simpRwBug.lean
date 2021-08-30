open Nat

theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) :=
  Nat.recOn (motive := fun k => m + n + k = m + (n + k)) k rfl (fun k ih => by simp [Nat.add_succ, ih]; done)
