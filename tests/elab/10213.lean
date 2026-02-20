/-!
Tests that `@[csimp]` rejects constant replacements with concrete universe parameters
-/

noncomputable def funnyChoice (x : α) : α := Classical.choice ⟨x⟩

/--
error: invalid 'csimp' theorem, only constant replacement theorems (e.g., `@f = @g`) are currently supported.
-/
#guard_msgs in
@[csimp]
theorem bad_csimp : @funnyChoice.{0} = @id.{0} := rfl

/--
error: Tactic `native_decide` failed. Error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'funnyChoice', which is 'noncomputable'
-/
#guard_msgs in
example : False := by
  have : funnyChoice 2 = funnyChoice 3 := rfl
  have : funnyChoice 2 ≠ funnyChoice 3 := by native_decide
  contradiction
