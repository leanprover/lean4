/-!
# Issue #12242: grind fails when hypotheses contain metavariables

When `refine` introduces metavariables that appear in both hypotheses and the target,
`grind` should be able to close the goal. Previously, `abstractMVars` only abstracted
metavariables in the target, creating a disconnect between the target (using an fvar)
and hypotheses (still using the mvar).
-/

-- Original example from the issue
theorem grind_mvar_fail_2 (a res : Int) :
    ∃ x : Int,
      (a = x) →
      (x = res) →
      (x = res) := by
  refine ⟨?_, ?_⟩
  rotate_left
  intro h h2
  grind
  repeat constructor

-- Simpler version: mvar in hypothesis directly proves goal
theorem grind_mvar_simple (a : Nat) :
    ∃ x : Nat, (x = a) → (x = a) := by
  refine ⟨?_, ?_⟩
  rotate_left
  intro h
  grind
  exact a

-- Multiple hypotheses sharing the same mvar
theorem grind_mvar_chain (a b c : Nat) :
    ∃ x : Nat, (a = x) → (x = b) → (a = b) := by
  refine ⟨?_, ?_⟩
  rotate_left
  intro h1 h2
  grind
  exact a

-- Mvar in a more complex expression
theorem grind_mvar_complex (a b : Int) :
    ∃ x : Int, (a = x) → (x = b) → (a = b) := by
  refine ⟨?_, ?_⟩
  rotate_left
  intro h1 h2
  grind
  exact a
