import Lean

/-!
This test checks which error inline code reports when one of its parts fails.

Inline code that has no closing delimiter is reported as unterminated. A failure of the parser for
the whitespace after the closing delimiter is reported with that parser's own error.
-/

open Lean Doc Parser

/-- Runs `p` on `input` and prints its errors. -/
def report (p : ParserFn) (input : String) : IO Unit := do
  let ictx := mkInputContext input "<input>"
  let env : Environment ← mkEmptyEnvironment
  let s := p.run ictx {env, options := {}} (getTokenTable env) (mkParserState input)
  for (p, _, e) in s.allErrors do
    IO.println s!"@{p.byteIdx}: {e}"

-- The code has no closing delimiter.
/--
info: @2: unterminated inline code; expected '`'
-/
#guard_msgs in
#eval report (codeFn {}) "`a"

-- The code is closed, and the parser for the whitespace after it fails.
/--
info: @5: tail failed
-/
#guard_msgs in
#eval report (codeFn { tail := fun _ s => s.mkUnexpectedError "tail failed" }) "`a` b"
