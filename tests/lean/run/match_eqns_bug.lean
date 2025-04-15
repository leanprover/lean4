inductive Vec (α : Type u) : Nat → Type u
  | zero : Vec α 0
  | cons : α → Vec α n → Vec α (n+1)

def g (n : Nat) (v w : Vec α n) : Nat :=
  match v, w with
  | .zero, _  => 1
  | _, .cons _ (.cons _ _ ) => 2
  | _, _ => 3

example (h : g a b c = 4) : False := by
  unfold g at h
  split at h <;> contradiction
