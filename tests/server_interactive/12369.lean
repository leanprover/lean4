/-!
# Regression test for InfoView on `rcases`-family tactics

After an `rcases`-style `rfl` pattern substitutes a variable,
InfoView on later patterns should use the substituted local hypothesis, not an old free variable.

* https://github.com/leanprover/lean4/issues/12369
-/

/-! Testing that `0 ≤ a` prints as `0 ≤ b + 1` for `rcases`, used to fail. -/
example (h : ∃ a : Nat, (∃ b, a = b + 1) ∧ 0 ≤ a) : True := by
  rcases h with ⟨_, ⟨b, rfl⟩, hle⟩
                           --^ $/lean/plainGoal
  trivial

/-! Testing `rintro`. -/
example : (∃ a : Nat, (∃ b, a = b + 1) ∧ 0 ≤ a) → True := by
  rintro ⟨_, ⟨b, rfl⟩, hle⟩
                    --^ $/lean/plainGoal
  trivial

/-! Testing `.paren`. -/
example (h : ∃ a : Nat, (∃ b, a = b + 1) ∧ 0 ≤ a) : True := by
  obtain ⟨_, ⟨b, rfl⟩, (hle)⟩ := h
                     --^ $/lean/plainGoal
  trivial

/-! Testing `.clear` after `.alts`. Hypothesis `n = m` should be cleared. -/
example (n m : Nat) (h : n = m) : True := by
  rcases n, h with ⟨_ | _, -⟩
                         --^ $/lean/plainGoal
  trivial
  trivial

/-! Testing `.alts`. `a = 1 ∨ a = 2` prints `b + 1 = 1` and `b + 1 = 2` respectively. -/
example (h : ∃ a : Nat, (∃ b, a = b + 1) ∧ (a = 1 ∨ a = 2)) : True := by
  rcases h with ⟨_, ⟨b, rfl⟩, h1 | h2⟩
                            --^ $/lean/plainGoal
                                 --^ $/lean/plainGoal
  trivial
  trivial
