/-!
Regression tests for #15053: on the line after the last tactic of a nested tactic block that ends
an incremental tactic step (e.g. an empty `·` bullet inside `have ... := by`), the goal view must
show the nested block's goal, not the state after the enclosing tactic. The nested nodes used to
lose the trailing whitespace trimmed for incremental reuse.
-/

-- Issue example 1: empty `·` inside a nested `by`; expected `⊢ B` right after `·` (col 5) and on
-- the next line at cols 7 and 5; the outer state is shown at col 3 (dedented relative to `·`) and
-- at cols 0 and 2 (the `have` column).
example (A B C : Prop) (hA : A) : A ↔ C := by
  have hAB : A ∧ B := by
    constructor
    · assumption
    ·
   --^ $/lean/plainGoal
      -- cursor here
     --^ $/lean/plainGoal
   --^ $/lean/plainGoal
 --^ $/lean/plainGoal
--⬑ $/lean/plainGoal

-- Same, but with a following outer tactic
example (A B C : Prop) (hA : A) : A ↔ C := by
  have hAB : A ∧ B := by
    constructor
    · assumption
    ·
      -- cursor here
     --^ $/lean/plainGoal
   --^ $/lean/plainGoal
  sorry

-- Control: empty `·` directly in the top-level block; expected `⊢ B` at cols 3, 4 and 2
example (A B : Prop) (hA : A) (hB : B) : A ∧ B := by
  constructor
  · assumption
  ·
 --^ $/lean/plainGoal
    -- cursor here
   --^ $/lean/plainGoal
 --^ $/lean/plainGoal

-- Non-empty nested blocks are affected as well: the last nested tactic must still own the
-- following lines at its own column or deeper.
example (A B C : Prop) (hA : A) (hB : B) : A ↔ C := by
  have hAB : A ∧ B := by
    constructor
    · assumption
    · skip
      -- cursor here
     --^ $/lean/plainGoal
   --^ $/lean/plainGoal
 --^ $/lean/plainGoal

example : False := by
  have : True := by
    skip
    -- cursor here
   --^ $/lean/plainGoal
 --^ $/lean/plainGoal
  sorry

-- Term-level nested `by` ending the tactic step
example : True := by
  exact id <| by
    skip
    -- cursor here
   --^ $/lean/plainGoal

-- Nested `by` that does not end the tactic step (unaffected)
example : True ∧ True := by
  refine ⟨?_, by
    skip
    -- cursor here
   --^ $/lean/plainGoal
    ⟩
  trivial
