/-!
Regression tests for #7135: the goal view while a tactic is being typed and does not parse yet.

After a parse error, the parser skips input up to the next command it can parse, and the skipped
input belongs to no syntax tree. On the first line of skipped input, the goal view now shares the
goals of the syntax before it, as if the input were trailing whitespace. A tactic cut short by the
parse error, whose goal error recovery then closed with `sorry`, keeps that goal visible, as for
other errors in a tactic's own term (#7136).
-/

-- Issue example: an abbreviation being typed (`\<` for `⟨`) cannot be lexed; expected the state
-- after `skip` (`⊢ True`), on the backslash and after `\<`
example : True := by
  skip
  exact \<
      --^ $/lean/plainGoal
        --^ $/lean/plainGoal

-- Skipped input starting right after the last token; expected `⊢ True`
example : True := by
  obtain ⟨x, y\
             --^ $/lean/plainGoal

-- Skipped input after a complete tactic (`obtain` alone parses); expected `⊢ True`
example : True := by
  obtain \
        --^ $/lean/plainGoal

-- Skipped input on a new line after a complete tactic, here a bullet being typed; expected the
-- state after `constructor`, as in whitespace there
example : True ∧ True := by
  constructor
  \.
  --^ $/lean/plainGoal
  · trivial

-- Inside a bullet and inside a nested block; expected the bullet's goal and `h`'s goal
example : True ∧ True := by
  constructor
  · exact \<
          --^ $/lean/plainGoal
  · trivial

example : False := by
  have h : True := by
    skip
    exact \<
          --^ $/lean/plainGoal
  trivial

-- Partial syntax ending at the next command: the goal that error recovery closed stays visible
example : Nat → True := by
  intro (
       --^ $/lean/plainGoal

example : Nat × Nat → True := by
  intro ⟨x, 
          --^ $/lean/plainGoal

example : True := by
  exact 
      --^ $/lean/plainGoal

example : Nat → True := by
  exact fun x =>
              --^ $/lean/plainGoal

-- on the first of two goals; expected both goals
example : True ∧ True := by
  constructor
  exact 
      --^ $/lean/plainGoal

-- with a proof nested in the term; expected `⊢ True ∧ True`
example : True ∧ True := by
  exact ⟨by trivial, (
                    --^ $/lean/plainGoal

-- Unchanged: a complete tactic; expected no goals
example : True := by
  exact trivial
             --^ $/lean/plainGoal

-- Unchanged: an unknown tactic name, which parses as the `unknown` tactic; expected `⊢ True`
example : True := by
  skip
  ski
   --^ $/lean/plainGoal

-- Unchanged: partial tactics that did not fail; `simp only [h]` closes the goal (no goals),
-- `refine` creates a goal for `?_`, and the bodies of `case` and `<;>` are missing
example (a b : Nat) (h : a = b) : b = a := by
  simp only [h, 
              --^ $/lean/plainGoal

example : True ∧ True := by
  refine ⟨?_, 
            --^ $/lean/plainGoal

example : True ∧ True := by
  constructor
  case left =>
            --^ $/lean/plainGoal

example : True ∧ True := by
  constructor <;>
               --^ $/lean/plainGoal

-- Unchanged: a partial tactic that closed a goal whose statement or context already contains an
-- error (here `Nat.succ "x"`); expected no goals
example (a b : Nat) (h : a = b) : b + Nat.succ "x" = a + Nat.succ "x" := by
  simp only [h, 
              --^ $/lean/plainGoal

example (a b : Nat) (h : a = b) (c : Nat := Nat.succ "x") : b + c = a + c := by
  simp only [h, 
              --^ $/lean/plainGoal

-- The same with the cursor inside the cut-short tactic
example : Nat → True := by
  intro (
  --^ $/lean/plainGoal

-- Unchanged: dedented after a cut-short tactic in a bullet, the state after the bullet; expected
-- `⊢ True` with the case `right`
example : True ∧ True := by
  constructor
  · exact 
  -- cursor here
--^ $/lean/plainGoal

-- Unchanged: later lines of skipped input hold tactics that never ran; expected nothing (`null`)
example : True := by
  skip
  exact \<
  skip
    --^ $/lean/plainGoal

-- Unchanged: the next command after skipped input; expected both goals
example : True := by
  exact \<

example : True ∧ True := by
  constructor
           --^ $/lean/plainGoal
  all_goals trivial

-- Not handled: skipped input on the line after a tactic cut short. The cursor is past the line of
-- `exact`, so the state after it is shown (no goals).
example : True := by
  exact
  \<
  --^ $/lean/plainGoal

-- Skipped input at the end of the file; expected `⊢ True`
example : True := by
  skip
        --v $/lean/plainGoal
  exact \<