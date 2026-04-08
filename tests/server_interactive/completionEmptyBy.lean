prelude
import Init.Notation

/-
Tests for tactic completion in empty `by` blocks (no indented tactics follow).

Tests cover:
- Top-level `by`
- Nested `by` inside expressions (e.g. `id <| have := by`)
- Completion at various columns on the line below `by`

Note: `--^` tests at the column of `^`; `--⬑` tests at the column of `--` itself (for column 0).
To test a column on the line below `by`, we place an indented comment there so that the tested
column falls within the leading whitespace (matching how completionTactics.lean works).
-/

/-- A docstring -/
syntax (name := skip) "skip" : tactic

-- ===== On the `by` token itself (no completions expected) =====

-- column 20 on `by` line (end of `by` token, before whitespace)
example : True := by
                  --^ completion

-- column 20 on nested `by` line (end of `by` token, before whitespace)
example : True := id <|
  have : True := by
                 --^ completion

-- ===== Top-level `by`, non-indented content following =====

-- column 21 on line below `by`
example : True := by
                      -- below by
                   --^ completion
sorry

-- column 0 on line below `by`
example : True := by
   -- below by
--⬑ completion
sorry

-- column 2 on line below `by`
example : True := by
   -- below by
--^ completion
sorry

-- ===== Top-level `by`, no tactics following =====

-- column 21 on line below `by`
example : True := by
                      -- below by
                   --^ completion

-- column 0 on line below `by`
example : True := by
   -- below by
--⬑ completion

-- column 2 on line below `by`
example : True := by
   -- below by
--^ completion

-- ===== Nested `by`, content following =====

-- column 21 on line below `by`
example : True := id <|
  have : True := by
                      -- below by
                   --^ completion
  sorry

-- column 2 on line below `by` (at column of `have` line)
example : True := id <|
  have : True := by
     -- below by
  --^ completion
  sorry

-- column 0 on line below `by`
example : True := id <|
  have : True := by
   -- below by
--⬑ completion
  sorry

-- column 4 on line below `by` (indented past `have` but not past `by`)
example : True := id <|
  have : True := by
       -- below by
    --^ completion
  sorry

-- ===== Nested `by`, no tactics following =====

-- column 21 on line below `by`
example : True := id <|
  have : True := by
                      -- below by
                   --^ completion

-- column 2 on line below `by` (at column of `have` line)
example : True := id <|
  have : True := by
     -- below by
  --^ completion

-- column 0 on line below `by`
example : True := id <|
  have : True := by
   -- below by
--⬑ completion

-- column 4 on line below `by`
example : True := id <|
  have : True := by
       -- below by
    --^ completion
