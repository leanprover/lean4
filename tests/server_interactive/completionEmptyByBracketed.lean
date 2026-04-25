prelude
import Init.Notation

/-
Tests for tactic completion in empty *bracketed* tactic blocks `by { ... }`.

`tacticSeqBracketed` is special: its body has no position information but the
enclosing braces do. Tactics inserted into an empty bracketed block can appear
at any column between the braces (the parser uses `withoutPosition` internally
to disable the usual `checkColGt` constraint that applies to the non-bracketed
form `by <newline>\n  ...`). The completion engine must therefore bypass its
standard "canonical column" indentation check when the cursor is inside an
empty `{ ... }` block.

Other tactic block openers (`·`, `focus`, `case`, `decreasing_by`, `finally`)
are not exercised here: they either share the same `tacticSeqIndentGt` parser
as `by` (and thus share behavior with `completionEmptyBy.lean`) or use a plain
`tacticSeq` (where the regular canonical-column check from `by` applies
correctly).
-/

/-- A docstring -/
syntax (name := skip) "skip" : tactic
/-- A docstring -/
syntax (name := refine) "refine " term : tactic
/-- A docstring -/
syntax (name := intro) "intro " term : tactic

-- ===== Bracketed tactic block inside `by` =====

-- Aligned braces at col 2. Cursor at canonical col 4.
example : True := by
  {
     -- below
  --^ completion
  }

-- Aligned braces at col 2. Cursor at col 6 (deeper than canonical).
example : True := by
  {
       -- below
    --^ completion
  }

-- Aligned braces at col 2. Cursor at col 0.
example : True := by
  {
     -- below
--⬑ completion
  }

-- Misaligned braces: opener at col 2, closer at col 6. Cursor at col 4.
example : True := by
  {
     -- below
  --^ completion
      }

-- Opener inline after by on the example line. Closer at col 0. Cursor at col 2.
example : True := by {
   -- below
--^ completion
}
