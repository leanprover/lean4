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

-- ===== Cursor before `by` on the same line (no completions expected) =====

-- Only the trailing whitespace past an opener token (here `by`) should offer completions. A
-- cursor in whitespace that precedes the opener on the same line must not — that whitespace is
-- part of the surrounding term, not the tactic block.

-- column 18 between `:=` and `by` (cursor is before `by` on the same line)
example : True :=      by
                --^ completion

-- column 4 in leading indent of a line whose only token is `by`
example : True :=
     by
  --^ completion

-- column 18 before nested `by`, on the same line as `by`
example : True := id <|
  have : True :=      by
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
