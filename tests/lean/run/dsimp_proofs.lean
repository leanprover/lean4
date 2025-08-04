@[simp]
theorem foo (i : Nonempty α) : Nonempty.intro (Classical.choice i) = i := rfl

/-- error: `dsimp` made no progress -/
#guard_msgs in
example : Classical.choice (Nonempty.intro (Classical.choice instNonemptyFloat)) = 0 := by
  dsimp
