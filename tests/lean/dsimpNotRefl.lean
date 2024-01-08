/-! # Error messages when passing non-`rfl` theorems to `dsimp` -/

theorem t : True := .intro

-- This should fail, as `t` is not a proof by reflexivity.
example : True := by
  dsimp [t]

-- This should fail, as `True.intro` is not a proof by reflexivity.
example : True := by
  dsimp [True.intro]

-- This should work as `Nat.zero` is not a theorem.
example : 0 = 0 := by
  dsimp [Nat.zero]

-- This should work as `Nat.add_zero` is proven by `rfl`.
example (n : Nat) : n + 0 = n := by
  dsimp [Nat.add_zero]

-- This should fail as `t` is not a proof by reflexivity.
example (n : Nat) : n + 0 = n := by
  dsimp [Nat.add_zero, t]
