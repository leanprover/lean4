example (a : Nat) : (a - 8000) + 1 = Nat.succ (a - 8000) := by
  rfl

theorem mwe (a : Nat) : (a - 100000000) + 1 <= 1 := by
  apply Nat.succ_le_succ
  sorry

@[irreducible]
def someConstant : Nat := 100000000

theorem mwe' (a : Nat) : (a - someConstant) + 1 <= someConstant + 1 := by
  apply Nat.succ_le_succ
  sorry

theorem mwe'' (a : Nat) : Nat.add (a - 100000000) 1 <= Nat.zero.succ := by
  apply Nat.succ_le_succ
  sorry
