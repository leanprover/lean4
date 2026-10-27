/-!
Regression tests for #7136: when the term given to `exact` or `apply` fails to elaborate, the goal
view must keep showing the goal. The term elaborates to an error `sorry`, which closes the goal, so
the goal view used to show "no goals" (or the next goal) while the term was being typed.
-/

example : True ∧ False := by
  exact true_
           --^ $/lean/plainGoal

-- A term that is still missing
example : True ∧ False := by
  exact
     --^ $/lean/plainGoal

example : True ∧ False := by
  apply true_
           --^ $/lean/plainGoal

example : 1 = 1 := by
  apply rf
        --^ $/lean/plainGoal

example : True := by
  apply
     --^ $/lean/plainGoal

-- An error in part of the term
example : True ∧ True := by
  exact ⟨trivial, foo_⟩
                     --^ $/lean/plainGoal

-- The goal being closed stays first, rather than the next goal being shown alone.
example : True ∧ True := by
  constructor
  exact foo_
          --^ $/lean/plainGoal
  exact trivial

-- A type mismatch already kept the goal; a correct term still closes it.
example : True ∧ False := by
  exact true
          --^ $/lean/plainGoal

example : True := by
  exact trivial
             --^ $/lean/plainGoal

-- An error in the pattern of `obtain`
example : True := by
  obtain y|z := a
               --^ $/lean/plainGoal

-- Other tactics that close the goal with the term
example : True := by
  refine foo_
           --^ $/lean/plainGoal

example : True := by
  obtain ⟨x, y⟩ := foo_
                     --^ $/lean/plainGoal

example (f : Nat → False) : True := by
  cases f foo_
            --^ $/lean/plainGoal

example : True ∧ True := by
  constructor <;> exact foo_
                          --^ $/lean/plainGoal

-- A term spanning several lines, with the cursor on an earlier line
example : True ∧ True := by
  exact ⟨foo_,
            --^ $/lean/plainGoal
    trivial⟩

/-! Closed goals that must stay closed in the goal view. -/

-- An error `sorry` that is already in the goal does not count.
example : True ∨ foo_ := by
  exact Or.inl trivial
                    --^ $/lean/plainGoal

-- Nor does one from a hypothesis.
example : True ∧ True := by
  have h : True ∧ foo_ := sorry
  constructor
  exact h.1
         --^ $/lean/plainGoal
  trivial

-- `have` with an error in its statement creates the next goal; only that one is shown.
example : True := by
  have h : True ∧ foo_ := sorry
                             --^ $/lean/plainGoal
  trivial

-- After a `have ... := by` block whose nested `exact` failed: the state after `have`.
example : True := by
  have h : True := by
    exact foo_
  -- next tactic here
--^ $/lean/plainGoal
  exact h

-- Tactics that leave new goals show those.
example : True ∧ True := by
  refine ⟨foo_, ?_⟩
                 --^ $/lean/plainGoal
  trivial

example (h : True → 1 = 1 → False) : False := by
  apply h foo_
            --^ $/lean/plainGoal

-- A `sorry` written by the user is not an error.
example : True := by
  exact sorry
           --^ $/lean/plainGoal

-- An argument of `apply` that is elaborated only after the goal is assigned
example : True ∧ True := by
  apply id ⟨foo_, trivial⟩
                        --^ $/lean/plainGoal

-- After a bullet that leaves its goal unsolved, the state after the bullet (see also 15053.lean).
example : True ∧ True := by
  constructor
  · skip
    -- cursor here
 --^ $/lean/plainGoal
  · trivial

-- Proofs nested in the term do not turn this off.
example : True ∧ True := by
  exact ⟨by trivial, foo_⟩
                        --^ $/lean/plainGoal

example : True ∧ True := by
  exact ⟨trivial, by exact foo_⟩
                              --^ $/lean/plainGoal

-- On the next line, where the next tactic will be typed, the state after the tactic is shown as
-- it is, as it will be once that tactic has been started.
example : True ∧ True := by
  constructor
  exact foo_
  -- next tactic here
--^ $/lean/plainGoal
  trivial

-- An error in the statement of a lemma used does not count.
theorem bad : True ∧ Nat.foo_ := sorry

example : True := by
  exact bad.1
           --^ $/lean/plainGoal

-- A tactic that admits the goal itself when it fails, like one that throws, keeps it visible.
example (x : Nat) : x = 3 := by
  grind
     --^ $/lean/plainGoal
