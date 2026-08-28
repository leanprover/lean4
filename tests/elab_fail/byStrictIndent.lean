-- Un-indented tactic after top-level `by` parses as empty `by` (unsolved goals)
-- followed by a command parse error for the stray tactic.
theorem byTopLevelBad (n : Nat) (h : n > 1) : n > 1 := by
exact h -- unsolved goals + unexpected identifier

-- Nested `by` without indentation: inner `by` is empty, `sorry` continues in outer scope.
theorem byNestedStrictIndent (n : Nat) (h : n > 0) : n > 1 := by
  have helper : n > 1 := by
  sorry -- part of outer `by`; inner `by` is empty (unsolved goals)
  sorry

--
theorem byNestedBad₁ (n : Nat) (h : n > 0) : n > 1 := by
  have helper : n > 1 := by
    sorry
   sorry -- expected command
  sorry

theorem byNestedBad₂ (n : Nat) (h : n > 0) : n > 1 := by
  have helper : n > 1 := by
    sorry
      sorry -- expected command
  sorry

-- When stacking multiple `by` invocations on one line, the indentation of the
-- tactic block is checked against the innermost `withPosition` point (the column
-- of the innermost `have`/`let`/etc.), not against the outermost `by`.
-- So indenting past the outer `by` is not enough if the inner `have` is further right.

-- Good: each tactic block is indented past its respective `have`
theorem byStackedGood : True := by
  have : True := by
    exact trivial
  exact this

-- Bad: tactic is indented past the outer `by` (column 0) but not past `have` (column 27)
-- Inner `by` is empty (unsolved goals), stray tactics produce command parse errors.
theorem byStackedBad₁ : True := by have : True := by
  exact trivial -- unsolved goals + unexpected identifier
  exact this

-- Bad: same issue with deeper stacking
theorem byStackedBad₂ : True := by have : True := by have : True := by
  exact trivial -- unsolved goals + unexpected identifier
  exact this

-- When `by` is inside a command that sets a position (like `#guard_msgs`),
-- `withPosition` at the command level checks against the command's column.
-- The `trivial` at column 2 must be > column of `#guard_msgs` (column 0).
#guard_msgs (drop info) in
example : True := by
  trivial

-- Command-wrapping-command on one line: the proof needs to be indented
-- past the outer command (`#guard_msgs`, col 0), not the inner (`example`).
-- `#guard_msgs in` uses `commandParser` directly, not `topLevelCommandParserFn`,
-- so the inner command does not get its own `withPosition` scope.
#guard_msgs (drop info) in example : True := by
  trivial

-- Same but with the inner command indented
#guard_msgs (drop info) in
  example : True := by
    trivial

-- Bad: tactic at column 0 inside #guard_msgs is not indented past the command
#guard_msgs (drop info) in
example : True := by
trivial -- unsolved goals + unexpected identifier

-- Bad: tactic at column 0 inside inline #guard_msgs
#guard_msgs (drop info) in example : True := by
trivial -- unsolved goals + unexpected identifier

-- Indented commands inside section: with `withPosition` at command level,
-- the position is saved at the command's column, not at column 0.
-- So proofs must be indented past the command, not just past column 0.
section
  theorem indentedGood : True := by
    trivial
end

-- Bad: tactic at column 2 is not indented past `theorem` (column 2)
section
  theorem indentedBad : True := by
  trivial -- unsolved goals + unexpected identifier
end

-- Indented non-tactic content: `123` doesn't parse as a tactic, so the
-- empty-by fallback fires (unsolved goals) and `123` is tried as a command.
-- This matches the behavior of non-tactic content on subsequent lines.
theorem fallbackOnNonTactic : True := by
  123 -- unsolved goals + unexpected token

-- For comparison: non-tactic on second line (after a valid tactic).
-- Same pattern: `123` falls out of the tactic block and gets a command error.
theorem fallbackOnNonTacticSecondLine : True := by
  skip
  123 -- unsolved goals + unexpected token
