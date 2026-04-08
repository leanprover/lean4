-- dsimp can close goals by rfl
-- but metadata would inhibit this

-- Easy case: no metadata, so expected to work even without fix.
example : ∀ (x : α × α), x = id x := by
  intro p
  dsimp

-- The `intro` adds `noImplicitLambda` metadata. Without fix, a `rfl` is needed.
example : ∀ (x : α × α), x = id x := by
  intro (x, y)
  dsimp

-- The `have` adds `noImplicitLambda` metadata. Without fix, `dsimp` makes no progress.
example {α : Type _} (n : α) : n = n := by
  have := 0
  dsimp
