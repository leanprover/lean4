example (x₁ x₂ y₁ y₂ : Nat) : (x₁ + x₂) + (y₁ + y₂) = (x₁ + y₁) + (x₂ + y₂) := by
  calc (x₁ + x₂) + (y₁ + y₂)
      = x₁ + (x₂ + (y₁ + y₂)) := by rw [Nat.add_assoc]
    _ = x₁ + (y₁ + (x₂ + y₂)) := by rw [Nat.add_left_comm x₂ y₁ y₂]
    _ = (x₁ + y₁) + (x₂ + y₂) := by rw [Nat.add_assoc]


example (n x₁ x₂ y₁ y₂ : Nat) : n = 0 → (x₁ + x₂) + (y₁ + y₂) = (x₁ + y₁) + (x₂ + y₂) := by
  intro h
  induction n with
  | zero =>
    calc (x₁ + x₂) + (y₁ + y₂)
       = x₁ + (x₂ + (y₁ + y₂)) := by rw [Nat.add_assoc]
     _ = x₁ + (y₁ + (x₂ + y₂)) := by rw [Nat.add_left_comm x₂ y₁ y₂]
     _ = (x₁ + y₁) + (x₂ + y₂) := by rw [Nat.add_assoc]
  | succ _ _ => contradiction
