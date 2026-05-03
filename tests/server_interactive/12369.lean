/-!
After an `rcases`-style `rfl` pattern substitutes a variable,
info view on later patterns should use the substituted local hypothesis, not an old free variable.
-/

example (h : ∃ a : Nat, (∃ b, a = b + 1) ∧ 0 ≤ a) : True := by
  rcases h with ⟨_, ⟨b, rfl⟩, hle⟩
                           --^ $/lean/plainGoal
  trivial

example : (∃ a : Nat, (∃ b, a = b + 1) ∧ 0 ≤ a) → True := by
  rintro ⟨_, ⟨b, rfl⟩, hle⟩
                    --^ $/lean/plainGoal
  trivial

example (h : ∃ a : Nat, (∃ b, a = b + 1) ∧ 0 ≤ a) : True := by
  obtain ⟨_, ⟨b, rfl⟩, (hle)⟩ := h
                     --^ $/lean/plainGoal
  trivial
