def foo : (n : Nat) → (i : Fin n) → Bool
  | 0, _ => false
  | 1, _ => false
  | _+2, _ => foo 1 ⟨0, Nat.zero_lt_one⟩

def bar : (n : Nat) → (i : Fin n) → Bool
  | 0, _ => false
  | 1, _ => false
  | _+2, _ => bar 1 ⟨0, Nat.zero_lt_one⟩
termination_by n => n
